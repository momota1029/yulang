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
