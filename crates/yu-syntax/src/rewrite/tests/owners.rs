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
