use super::*;

#[test]
fn parenthesized_primary_owns_its_sequence_and_outer_ml_tail() {
    let source = "(a,b;c) d";
    let (green, exit) = run(source);
    assert_eq!(green.to_string(), source);
    assert!(matches!(exit, Some(Err(Either::Right(_)))));

    let root = SyntaxNode::new_root(green);
    let outer = root
        .children()
        .find(|node| node.kind() == SyntaxKind::OperatorChain)
        .expect("outer expression chain");
    let group = outer
        .children()
        .find(|node| node.kind() == SyntaxKind::ParenthesizedExpression)
        .expect("parenthesized primary");
    assert_eq!(
        group
            .children()
            .filter(|node| node.kind() == SyntaxKind::OperatorChain)
            .count(),
        3
    );
    assert_eq!(
        outer
            .children()
            .filter(|node| node.kind() == SyntaxKind::MlArgument)
            .count(),
        1
    );
    assert_eq!(
        root.descendants_with_tokens()
            .filter_map(|element| element.into_token())
            .map(|token| token.kind())
            .collect::<Vec<_>>(),
        [
            SyntaxKind::LParen,
            SyntaxKind::Identifier,
            SyntaxKind::Comma,
            SyntaxKind::Identifier,
            SyntaxKind::Semicolon,
            SyntaxKind::Identifier,
            SyntaxKind::RParen,
            SyntaxKind::Whitespace,
            SyntaxKind::Identifier,
        ]
    );
    assert!(
        !root
            .descendants()
            .any(|node| matches!(node.kind(), SyntaxKind::Missing | SyntaxKind::Error))
    );
}

#[test]
fn call_and_index_own_valid_multiple_item_sequences() {
    let source = "f(a,b;c)[x,y;z]";
    let (green, exit) = run(source);
    assert_eq!(green.to_string(), source);
    assert!(matches!(exit, Some(Err(Either::Right(_)))));

    let root = SyntaxNode::new_root(green);
    let outer = root
        .children()
        .find(|node| node.kind() == SyntaxKind::OperatorChain)
        .expect("outer expression chain");
    let call = outer
        .children()
        .find(|node| node.kind() == SyntaxKind::CallTail)
        .expect("call tail");
    assert_eq!(
        call.children()
            .filter(|node| node.kind() == SyntaxKind::OperatorChain)
            .count(),
        3
    );
    let index = outer
        .children()
        .find(|node| node.kind() == SyntaxKind::IndexTail)
        .expect("index tail");
    assert_eq!(
        index
            .children()
            .filter(|node| node.kind() == SyntaxKind::IndexItem)
            .count(),
        3
    );
    let rparen = root
        .descendants_with_tokens()
        .filter_map(|element| element.into_token())
        .find(|token| token.kind() == SyntaxKind::RParen)
        .expect("call close");
    assert_eq!(
        rparen.parent().expect("call close owner").kind(),
        SyntaxKind::CallTail
    );
    let rbracket = root
        .descendants_with_tokens()
        .filter_map(|element| element.into_token())
        .find(|token| token.kind() == SyntaxKind::RBracket)
        .expect("index close");
    assert_eq!(
        rbracket.parent().expect("index close owner").kind(),
        SyntaxKind::IndexTail
    );
    assert!(
        !root
            .descendants()
            .any(|node| matches!(node.kind(), SyntaxKind::Missing | SyntaxKind::Error))
    );
}

#[test]
fn each_delimited_owner_accepts_an_empty_valid_sequence() {
    for (source, owner) in [
        ("()", SyntaxKind::ParenthesizedExpression),
        ("f()", SyntaxKind::CallTail),
        ("x[]", SyntaxKind::IndexTail),
    ] {
        let (green, exit) = run(source);
        assert_eq!(green.to_string(), source, "{source:?}");
        assert!(matches!(exit, Some(Err(Either::Right(_)))), "{source:?}");

        let root = SyntaxNode::new_root(green);
        let node = root
            .descendants()
            .find(|node| node.kind() == owner)
            .expect("delimited owner");
        assert_eq!(
            node.children()
                .filter(|node| matches!(
                    node.kind(),
                    SyntaxKind::OperatorChain | SyntaxKind::IndexItem
                ))
                .count(),
            0,
            "{source:?}"
        );
    }
}

#[test]
fn delimited_owner_emits_missing_close_before_handing_eof_outward() {
    for (source, owner) in [
        ("(a", SyntaxKind::ParenthesizedExpression),
        ("f(a /* tail */", SyntaxKind::CallTail),
        ("x[a", SyntaxKind::IndexTail),
        ("a.(x", SyntaxKind::ProjectionTupleTail),
        ("a.{x", SyntaxKind::ProjectionRecordTail),
    ] {
        let (green, exit) = run(source);
        assert_eq!(green.to_string(), source, "{source:?}");
        assert!(matches!(exit, Some(Err(Either::Right(_)))), "{source:?}");

        let root = SyntaxNode::new_root(green);
        let owner = root
            .descendants()
            .find(|node| node.kind() == owner)
            .expect("delimited owner");
        assert_eq!(
            owner.children().last().map(|node| node.kind()),
            Some(SyntaxKind::Missing),
            "{source:?}"
        );
        assert!(
            !root
                .descendants()
                .any(|node| node.kind() == SyntaxKind::Error),
            "{source:?}"
        );
    }
}

#[test]
fn delimited_owner_recovers_missing_items_before_separators() {
    for (source, owner) in [
        ("(,a)", SyntaxKind::ParenthesizedExpression),
        ("f(,a)", SyntaxKind::CallTail),
        ("f(a,,b)", SyntaxKind::CallTail),
        ("x[,a]", SyntaxKind::IndexTail),
        ("a.(,x)", SyntaxKind::ProjectionTupleTail),
        ("a.{,x}", SyntaxKind::ProjectionRecordTail),
    ] {
        let (green, exit) = run(source);
        assert_eq!(green.to_string(), source, "{source:?}");
        assert!(matches!(exit, Some(Err(Either::Right(_)))), "{source:?}");

        let root = SyntaxNode::new_root(green);
        let owner = root
            .descendants()
            .find(|node| node.kind() == owner)
            .expect("delimited owner");
        assert_eq!(
            owner
                .children()
                .filter(|node| node.kind() == SyntaxKind::Missing)
                .count(),
            1,
            "{source:?}"
        );
        assert!(
            !root
                .descendants()
                .any(|node| node.kind() == SyntaxKind::Error),
            "{source:?}"
        );
    }
}

#[test]
fn delimited_nud_recovery_retries_one_maximal_error_run() {
    for (source, owner, item_kind) in [
        (
            "(@@a)",
            SyntaxKind::ParenthesizedExpression,
            SyntaxKind::OperatorChain,
        ),
        ("f(@a)", SyntaxKind::CallTail, SyntaxKind::OperatorChain),
        ("x[@a]", SyntaxKind::IndexTail, SyntaxKind::IndexItem),
        (
            "a.(@x)",
            SyntaxKind::ProjectionTupleTail,
            SyntaxKind::OperatorChain,
        ),
        (
            "a.{@x}",
            SyntaxKind::ProjectionRecordTail,
            SyntaxKind::OperatorChain,
        ),
    ] {
        let (green, exit) = run(source);
        assert_eq!(green.to_string(), source, "{source:?}");
        assert!(matches!(exit, Some(Err(Either::Right(_)))), "{source:?}");

        let root = SyntaxNode::new_root(green);
        let owner = root
            .descendants()
            .find(|node| node.kind() == owner)
            .expect("delimited owner");
        assert_eq!(
            owner
                .children()
                .filter(|node| node.kind() == SyntaxKind::Error)
                .count(),
            1,
            "{source:?}"
        );
        assert_eq!(
            owner
                .children()
                .filter(|node| node.kind() == item_kind)
                .count(),
            1,
            "{source:?}"
        );
        assert!(
            !owner
                .descendants()
                .any(|node| node.kind() == SyntaxKind::Missing),
            "{source:?}"
        );
    }
}

#[test]
fn delimited_owner_consumes_wrong_closes_before_settling_its_own_close() {
    for (source, owner, wrong, missing) in [
        (
            "(a]",
            SyntaxKind::ParenthesizedExpression,
            SyntaxKind::RBracket,
            true,
        ),
        ("f(a])", SyntaxKind::CallTail, SyntaxKind::RBracket, false),
        ("x[a)", SyntaxKind::IndexTail, SyntaxKind::RParen, true),
        (
            "a.(x]",
            SyntaxKind::ProjectionTupleTail,
            SyntaxKind::RBracket,
            true,
        ),
        (
            "a.{x)",
            SyntaxKind::ProjectionRecordTail,
            SyntaxKind::RParen,
            true,
        ),
    ] {
        let (green, exit) = run(source);
        assert_eq!(green.to_string(), source, "{source:?}");
        assert!(matches!(exit, Some(Err(Either::Right(_)))), "{source:?}");

        let root = SyntaxNode::new_root(green);
        let owner = root
            .descendants()
            .find(|node| node.kind() == owner)
            .expect("delimited owner");
        let error = owner
            .children()
            .find(|node| node.kind() == SyntaxKind::Error)
            .expect("owner-local wrong-close error");
        assert_eq!(
            error.first_token().map(|token| token.kind()),
            Some(wrong),
            "{source:?}"
        );
        assert_eq!(
            owner
                .children()
                .any(|node| node.kind() == SyntaxKind::Missing),
            missing,
            "{source:?}"
        );
    }
}

#[test]
fn parenthesized_items_recover_a_same_line_missing_separator_without_ml() {
    let (green, exit) = run("(a b)");
    assert_eq!(green.to_string(), "(a b)");
    assert!(matches!(exit, Some(Err(Either::Right(_)))));

    let root = SyntaxNode::new_root(green);
    let group = root
        .descendants()
        .find(|node| node.kind() == SyntaxKind::ParenthesizedExpression)
        .expect("parenthesized expression");
    assert_eq!(
        group
            .children()
            .filter(|node| node.kind() == SyntaxKind::OperatorChain)
            .count(),
        2
    );
    assert_eq!(
        group
            .children()
            .filter(|node| node.kind() == SyntaxKind::Missing)
            .count(),
        1
    );
    assert_eq!(
        group
            .descendants()
            .filter(|node| node.kind() == SyntaxKind::MlArgument)
            .count(),
        0
    );
}

#[test]
fn block_comment_internal_newlines_are_not_parenthesized_layout() {
    let source = "(a /* outer\n inner */ b)";
    let (green, exit) = run(source);
    assert_eq!(green.to_string(), source);
    assert!(matches!(exit, Some(Err(Either::Right(_)))));

    let root = SyntaxNode::new_root(green);
    let group = root
        .descendants()
        .find(|node| node.kind() == SyntaxKind::ParenthesizedExpression)
        .expect("parenthesized expression");
    assert_eq!(
        group
            .children()
            .filter(|node| node.kind() == SyntaxKind::OperatorChain)
            .count(),
        2
    );
    assert_eq!(
        group
            .children()
            .filter(|node| node.kind() == SyntaxKind::Missing)
            .count(),
        1
    );
    assert!(
        !group
            .descendants()
            .any(|node| node.kind() == SyntaxKind::MlArgument)
    );
}

#[test]
fn delimited_items_accept_baseline_newlines_without_rescanning_the_handoff() {
    for (source, owner, item_kind) in [
        (
            "(a\nb)",
            SyntaxKind::ParenthesizedExpression,
            SyntaxKind::OperatorChain,
        ),
        ("f(a\nb)", SyntaxKind::CallTail, SyntaxKind::OperatorChain),
        ("x[a\nb]", SyntaxKind::IndexTail, SyntaxKind::IndexItem),
        (
            "a.(x\ny)",
            SyntaxKind::ProjectionTupleTail,
            SyntaxKind::OperatorChain,
        ),
        (
            "a.{x\ny}",
            SyntaxKind::ProjectionRecordTail,
            SyntaxKind::OperatorChain,
        ),
    ] {
        let (green, exit) = run(source);
        assert_eq!(green.to_string(), source, "{source:?}");
        assert!(matches!(exit, Some(Err(Either::Right(_)))), "{source:?}");

        let root = SyntaxNode::new_root(green);
        let owner = root
            .descendants()
            .find(|node| node.kind() == owner)
            .expect("delimited owner");
        assert_eq!(
            owner
                .children()
                .filter(|node| node.kind() == item_kind)
                .count(),
            2,
            "{source:?}"
        );
        assert!(
            !owner
                .descendants()
                .any(|node| node.kind() == SyntaxKind::Missing),
            "{source:?}"
        );
    }
}

#[test]
fn deeper_newlines_continue_the_current_delimited_item_chain() {
    for (source, owner, item_kind) in [
        (
            "(a\n  b)",
            SyntaxKind::ParenthesizedExpression,
            SyntaxKind::OperatorChain,
        ),
        ("f(a\n  b)", SyntaxKind::CallTail, SyntaxKind::OperatorChain),
        ("x[a\n  b]", SyntaxKind::IndexTail, SyntaxKind::IndexItem),
        (
            "a.(x\n  y)",
            SyntaxKind::ProjectionTupleTail,
            SyntaxKind::OperatorChain,
        ),
        (
            "a.{x\n  y}",
            SyntaxKind::ProjectionRecordTail,
            SyntaxKind::OperatorChain,
        ),
    ] {
        let (green, exit) = run(source);
        assert_eq!(green.to_string(), source, "{source:?}");
        assert!(matches!(exit, Some(Err(Either::Right(_)))), "{source:?}");

        let root = SyntaxNode::new_root(green);
        let owner = root
            .descendants()
            .find(|node| node.kind() == owner)
            .expect("delimited owner");
        assert_eq!(
            owner
                .children()
                .filter(|node| node.kind() == item_kind)
                .count(),
            1,
            "{source:?}"
        );
        assert_eq!(
            owner
                .descendants()
                .filter(|node| node.kind() == SyntaxKind::MlArgument)
                .count(),
            1,
            "{source:?}"
        );
        assert!(
            !owner
                .descendants()
                .any(|node| matches!(node.kind(), SyntaxKind::Missing | SyntaxKind::Error)),
            "{source:?}"
        );
    }
}

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
fn record_projection_spread_owns_exact_marker_and_rhs() {
    let source = "a.{left, ..rest, right}";
    let operators = OperatorTable::from_declarations([OperatorDeclaration::new(
        "..",
        OperatorFixities::new().with_prefix(BindingPower::scalar(70)),
    )])
    .expect("a direct rewrite operator table");
    let (green, exit) = run_with(source, &operators);
    assert_eq!(green.to_string(), source);
    assert!(matches!(exit, Some(Err(Either::Right(_)))));

    let root = SyntaxNode::new_root(green);
    let record = root
        .descendants()
        .find(|node| node.kind() == SyntaxKind::ProjectionRecordTail)
        .expect("record projection tail");
    let spreads = record
        .children()
        .filter(|node| node.kind() == SyntaxKind::ProjectionRecordSpreadItem)
        .collect::<Vec<_>>();
    assert_eq!(spreads.len(), 1);
    assert_eq!(
        spreads[0]
            .descendants_with_tokens()
            .filter_map(|element| element.into_token())
            .map(|token| token.kind())
            .collect::<Vec<_>>(),
        [
            SyntaxKind::Whitespace,
            SyntaxKind::DotDot,
            SyntaxKind::Identifier,
        ]
    );
    assert_eq!(
        spreads[0]
            .children()
            .filter(|node| node.kind() == SyntaxKind::OperatorChain)
            .count(),
        1
    );
    assert!(
        !record
            .descendants()
            .any(|node| matches!(node.kind(), SyntaxKind::Missing | SyntaxKind::Error))
    );
}

#[test]
fn record_projection_spread_recovers_its_mandatory_rhs() {
    for source in ["a.{..}", "a.{.., next}"] {
        let (green, exit) = run(source);
        assert_eq!(green.to_string(), source, "{source:?}");
        assert!(matches!(exit, Some(Err(Either::Right(_)))), "{source:?}");

        let root = SyntaxNode::new_root(green);
        let record = root
            .descendants()
            .find(|node| node.kind() == SyntaxKind::ProjectionRecordTail)
            .expect("record projection tail");
        let spread = record
            .children()
            .find(|node| node.kind() == SyntaxKind::ProjectionRecordSpreadItem)
            .expect("record spread item");
        assert_eq!(
            spread.children().last().map(|node| node.kind()),
            Some(SyntaxKind::Missing),
            "{source:?}"
        );
        assert!(
            !record
                .descendants()
                .any(|node| node.kind() == SyntaxKind::Error),
            "{source:?}"
        );
    }
}

#[test]
fn record_projection_spread_retries_one_invalid_rhs_run() {
    let source = "a.{..@rest}";
    let (green, exit) = run(source);
    assert_eq!(green.to_string(), source);
    assert!(matches!(exit, Some(Err(Either::Right(_)))));

    let root = SyntaxNode::new_root(green);
    let spread = root
        .descendants()
        .find(|node| node.kind() == SyntaxKind::ProjectionRecordSpreadItem)
        .expect("record spread item");
    assert_eq!(
        spread
            .children()
            .filter(|node| node.kind() == SyntaxKind::Error)
            .count(),
        1
    );
    assert_eq!(
        spread
            .children()
            .filter(|node| node.kind() == SyntaxKind::OperatorChain)
            .count(),
        1
    );
    assert!(
        !spread
            .children()
            .any(|node| node.kind() == SyntaxKind::Missing)
    );
}

#[test]
fn record_projection_spread_is_a_delimited_item_boundary() {
    for (source, expected_spreads, expected_missing, expected_error) in [
        ("a.{x ..rest}", 1, 1, 0),
        ("a.{..x ..rest}", 2, 1, 0),
        ("a.{@ ..rest}", 1, 0, 1),
    ] {
        let (green, exit) = run(source);
        assert_eq!(green.to_string(), source, "{source:?}");
        assert!(matches!(exit, Some(Err(Either::Right(_)))), "{source:?}");

        let root = SyntaxNode::new_root(green);
        let record = root
            .descendants()
            .find(|node| node.kind() == SyntaxKind::ProjectionRecordTail)
            .expect("record projection tail");
        assert_eq!(
            record
                .children()
                .filter(|node| node.kind() == SyntaxKind::ProjectionRecordSpreadItem)
                .count(),
            expected_spreads,
            "{source:?}"
        );
        assert_eq!(
            record
                .descendants()
                .filter(|node| node.kind() == SyntaxKind::Missing)
                .count(),
            expected_missing,
            "{source:?}"
        );
        assert_eq!(
            record
                .descendants()
                .filter(|node| node.kind() == SyntaxKind::Error)
                .count(),
            expected_error,
            "{source:?}"
        );
    }
}

#[test]
fn record_projection_spread_yields_to_an_accepted_dynamic_led() {
    let source = "a.{left .. right}";
    let operators = OperatorTable::from_declarations([OperatorDeclaration::new(
        "..",
        OperatorFixities::new().with_infix(BindingPower::scalar(40), BindingPower::new(40, [1])),
    )])
    .expect("a direct rewrite operator table");
    let (green, exit) = run_with(source, &operators);
    assert_eq!(green.to_string(), source);
    assert!(matches!(exit, Some(Err(Either::Right(_)))));

    let root = SyntaxNode::new_root(green);
    let record = root
        .descendants()
        .find(|node| node.kind() == SyntaxKind::ProjectionRecordTail)
        .expect("record projection tail");
    assert_eq!(
        record
            .children()
            .filter(|node| node.kind() == SyntaxKind::OperatorChain)
            .count(),
        1
    );
    assert!(!record.descendants().any(|node| matches!(
        node.kind(),
        SyntaxKind::ProjectionRecordSpreadItem | SyntaxKind::Missing | SyntaxKind::Error
    )));
}

#[test]
fn record_projection_spread_rhs_keeps_a_rejected_marker_for_the_owner() {
    for (source, expected_error) in [("a.{.. ..rest}", 0), ("a.{..@ ..rest}", 1)] {
        let (green, exit) = run(source);
        assert_eq!(green.to_string(), source, "{source:?}");
        assert!(matches!(exit, Some(Err(Either::Right(_)))), "{source:?}");

        let root = SyntaxNode::new_root(green);
        let record = root
            .descendants()
            .find(|node| node.kind() == SyntaxKind::ProjectionRecordTail)
            .expect("record projection tail");
        assert_eq!(
            record
                .children()
                .filter(|node| node.kind() == SyntaxKind::ProjectionRecordSpreadItem)
                .count(),
            2,
            "{source:?}"
        );
        assert_eq!(
            record
                .descendants()
                .filter(|node| node.kind() == SyntaxKind::Missing)
                .count(),
            2,
            "{source:?}"
        );
        assert_eq!(
            record
                .descendants()
                .filter(|node| node.kind() == SyntaxKind::Error)
                .count(),
            expected_error,
            "{source:?}"
        );
    }
}

#[test]
fn record_projection_spread_does_not_split_longer_operator_spellings() {
    let operators = OperatorTable::from_declarations([
        OperatorDeclaration::new(
            "...",
            OperatorFixities::new().with_prefix(BindingPower::scalar(70)),
        ),
        OperatorDeclaration::new(
            "..+",
            OperatorFixities::new().with_prefix(BindingPower::scalar(70)),
        ),
    ])
    .expect("a direct rewrite operator table");
    for source in ["a.{...rest}", "a.{..+rest}"] {
        let (green, exit) = run_with(source, &operators);
        assert_eq!(green.to_string(), source, "{source:?}");
        assert!(matches!(exit, Some(Err(Either::Right(_)))), "{source:?}");
        assert!(
            !SyntaxNode::new_root(green)
                .descendants()
                .any(|node| node.kind() == SyntaxKind::ProjectionRecordSpreadItem),
            "{source:?}"
        );
    }
}

#[test]
fn dot_projections_precede_field_dispatch_and_own_their_closes() {
    let source = "a.(x,y).{left,right}";
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
            SyntaxKind::ProjectionTupleTail,
            SyntaxKind::ProjectionRecordTail,
        ]
    );
    for (kind, close, expected_items) in [
        (SyntaxKind::ProjectionTupleTail, SyntaxKind::RParen, 2),
        (SyntaxKind::ProjectionRecordTail, SyntaxKind::RBrace, 2),
    ] {
        let projection = outer
            .children()
            .find(|node| node.kind() == kind)
            .expect("projection tail");
        assert_eq!(
            projection
                .children()
                .filter(|node| node.kind() == SyntaxKind::OperatorChain)
                .count(),
            expected_items
        );
        let close = projection
            .children_with_tokens()
            .filter_map(|element| element.into_token())
            .find(|token| token.kind() == close)
            .expect("projection close");
        assert_eq!(close.parent().expect("close owner").kind(), kind);
    }
    assert!(
        !root
            .descendants()
            .any(|node| matches!(node.kind(), SyntaxKind::Missing | SyntaxKind::Error))
    );
}

#[test]
fn index_item_accepts_ml_argument_without_separator_recovery() {
    let (green, exit) = run("x[a b]");
    assert_eq!(green.to_string(), "x[a b]");
    assert!(matches!(exit, Some(Err(Either::Right(_)))));

    let root = SyntaxNode::new_root(green);
    let outer_chain = root
        .children()
        .find(|node| node.kind() == SyntaxKind::OperatorChain)
        .expect("outer expression chain");
    let indexes = outer_chain
        .children()
        .filter(|node| node.kind() == SyntaxKind::IndexTail)
        .collect::<Vec<_>>();
    assert_eq!(indexes.len(), 1);
    let items = indexes[0]
        .children()
        .filter(|node| node.kind() == SyntaxKind::IndexItem)
        .collect::<Vec<_>>();
    assert_eq!(items.len(), 1);
    let item_chain = items[0]
        .children()
        .find(|node| node.kind() == SyntaxKind::OperatorChain)
        .expect("the index item owns its expression chain");
    let ml_arguments = item_chain
        .children()
        .filter(|node| node.kind() == SyntaxKind::MlArgument)
        .collect::<Vec<_>>();
    assert_eq!(ml_arguments.len(), 1);
    let argument_chain = ml_arguments[0]
        .children()
        .find(|node| node.kind() == SyntaxKind::OperatorChain)
        .expect("the ML argument owns its expression chain");
    assert_eq!(
        argument_chain
            .descendants_with_tokens()
            .filter_map(|element| element.into_token())
            .map(|token| token.text().to_owned())
            .collect::<Vec<_>>(),
        [" ", "b"]
    );
    assert_eq!(
        root.descendants_with_tokens()
            .filter_map(|element| element.into_token())
            .map(|token| token.kind())
            .collect::<Vec<_>>(),
        [
            SyntaxKind::Identifier,
            SyntaxKind::LBracket,
            SyntaxKind::Identifier,
            SyntaxKind::Whitespace,
            SyntaxKind::Identifier,
            SyntaxKind::RBracket,
        ]
    );
    let rbracket = root
        .descendants_with_tokens()
        .filter_map(|element| element.into_token())
        .find(|token| token.kind() == SyntaxKind::RBracket)
        .expect("index close");
    assert_eq!(
        rbracket.parent().expect("index close owner").kind(),
        SyntaxKind::IndexTail
    );
    assert!(
        !root
            .descendants()
            .any(|node| matches!(node.kind(), SyntaxKind::Missing | SyntaxKind::Error))
    );
}

#[test]
fn index_item_multiple_ml_arguments_stay_siblings() {
    let (green, exit) = run("x[a b c]");
    assert_eq!(green.to_string(), "x[a b c]");
    assert!(matches!(exit, Some(Err(Either::Right(_)))));

    let root = SyntaxNode::new_root(green);
    let outer_chain = root
        .children()
        .find(|node| node.kind() == SyntaxKind::OperatorChain)
        .expect("outer expression chain");
    let index = outer_chain
        .children()
        .find(|node| node.kind() == SyntaxKind::IndexTail)
        .expect("outer index tail");
    let item_chain = index
        .children()
        .find(|node| node.kind() == SyntaxKind::IndexItem)
        .and_then(|item| {
            item.children()
                .find(|node| node.kind() == SyntaxKind::OperatorChain)
        })
        .expect("the index item owns its expression chain");
    let arguments = item_chain
        .children()
        .filter(|node| node.kind() == SyntaxKind::MlArgument)
        .collect::<Vec<_>>();
    assert_eq!(arguments.len(), 2);
    for argument in arguments {
        assert!(
            !argument
                .descendants()
                .skip(1)
                .any(|node| node.kind() == SyntaxKind::MlArgument)
        );
    }
}

#[test]
fn index_item_ml_child_keeps_its_continuation_after_call() {
    let (green, exit) = run("x[a b(c) d]");
    assert_eq!(green.to_string(), "x[a b(c) d]");
    assert!(matches!(exit, Some(Err(Either::Right(_)))));

    let root = SyntaxNode::new_root(green);
    let outer_chain = root
        .children()
        .find(|node| node.kind() == SyntaxKind::OperatorChain)
        .expect("outer expression chain");
    let index = outer_chain
        .children()
        .find(|node| node.kind() == SyntaxKind::IndexTail)
        .expect("outer index tail");
    let item_chain = index
        .children()
        .find(|node| node.kind() == SyntaxKind::IndexItem)
        .and_then(|item| {
            item.children()
                .find(|node| node.kind() == SyntaxKind::OperatorChain)
        })
        .expect("the index item owns its expression chain");
    let arguments = item_chain
        .children()
        .filter(|node| node.kind() == SyntaxKind::MlArgument)
        .collect::<Vec<_>>();
    assert_eq!(arguments.len(), 2);
    assert!(
        arguments[0]
            .descendants()
            .any(|node| node.kind() == SyntaxKind::CallTail)
    );
    for argument in arguments {
        assert!(
            !argument
                .descendants()
                .skip(1)
                .any(|node| node.kind() == SyntaxKind::MlArgument)
        );
    }
}

#[test]
fn index_item_nested_call_keeps_close_owner_control() {
    let (green, exit) = run("x[a(b)]");
    assert_eq!(green.to_string(), "x[a(b)]");
    assert!(matches!(exit, Some(Err(Either::Right(_)))));

    let root = SyntaxNode::new_root(green);
    let outer_chain = root
        .children()
        .find(|node| node.kind() == SyntaxKind::OperatorChain)
        .expect("outer expression chain");
    let index = outer_chain
        .children()
        .find(|node| node.kind() == SyntaxKind::IndexTail)
        .expect("outer index tail");
    let items = index
        .children()
        .filter(|node| node.kind() == SyntaxKind::IndexItem)
        .collect::<Vec<_>>();
    assert_eq!(items.len(), 1);
    let item_chain = items[0]
        .children()
        .find(|node| node.kind() == SyntaxKind::OperatorChain)
        .expect("the index item owns its expression chain");
    let call = item_chain
        .children()
        .find(|node| node.kind() == SyntaxKind::CallTail)
        .expect("the index expression owns its nested call tail");
    assert_eq!(
        call.children()
            .filter(|node| node.kind() == SyntaxKind::OperatorChain)
            .count(),
        1
    );
    assert_eq!(
        root.descendants_with_tokens()
            .filter_map(|element| element.into_token())
            .map(|token| token.kind())
            .collect::<Vec<_>>(),
        [
            SyntaxKind::Identifier,
            SyntaxKind::LBracket,
            SyntaxKind::Identifier,
            SyntaxKind::LParen,
            SyntaxKind::Identifier,
            SyntaxKind::RParen,
            SyntaxKind::RBracket,
        ]
    );
    let rparen = root
        .descendants_with_tokens()
        .filter_map(|element| element.into_token())
        .find(|token| token.kind() == SyntaxKind::RParen)
        .expect("call close");
    assert_eq!(
        rparen.parent().expect("call close owner").kind(),
        SyntaxKind::CallTail
    );
    let rbracket = root
        .descendants_with_tokens()
        .filter_map(|element| element.into_token())
        .find(|token| token.kind() == SyntaxKind::RBracket)
        .expect("index close");
    assert_eq!(
        rbracket.parent().expect("index close owner").kind(),
        SyntaxKind::IndexTail
    );
    assert!(
        !root
            .descendants()
            .any(|node| matches!(node.kind(), SyntaxKind::Missing | SyntaxKind::Error))
    );
}
