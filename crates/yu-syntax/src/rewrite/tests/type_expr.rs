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
