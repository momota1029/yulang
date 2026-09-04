use super::*;

#[test]
fn if_c6_builds_direct_arm_topology_and_keeps_pre_keyword_trivia_outer() {
    let source = "  if x: a elsif y: b else: c";
    let (green, exit) = run(source);
    assert_eq!(green.to_string(), source);
    assert!(matches!(exit, Some(Err(Either::Right(_)))));

    let root = SyntaxNode::new_root(green);
    let outer = root
        .children()
        .find(|node| node.kind() == SyntaxKind::OperatorChain)
        .expect("outer expression chain");
    let if_expression = outer
        .children()
        .find(|node| node.kind() == SyntaxKind::IfExpression)
        .expect("if primary");
    assert_eq!(
        if_expression
            .children()
            .map(|node| node.kind())
            .collect::<Vec<_>>(),
        [SyntaxKind::IfArm, SyntaxKind::IfArm, SyntaxKind::ElseArm]
    );
    assert_eq!(
        if_expression
            .descendants_with_tokens()
            .filter_map(|element| element.into_token())
            .filter(|token| token.kind() == SyntaxKind::Whitespace && token.text() == "  ")
            .count(),
        0
    );
    assert_eq!(
        outer
            .children_with_tokens()
            .filter_map(|element| element.into_token())
            .filter(|token| token.kind() == SyntaxKind::Whitespace && token.text() == "  ")
            .count(),
        1
    );
    assert_eq!(
        if_expression
            .descendants_with_tokens()
            .filter_map(|element| element.into_token())
            .filter(|token| {
                matches!(
                    token.kind(),
                    SyntaxKind::IfKw | SyntaxKind::ElsifKw | SyntaxKind::ElseKw
                )
            })
            .map(|token| (token.kind(), token.text().to_owned()))
            .collect::<Vec<_>>(),
        [
            (SyntaxKind::IfKw, "if".to_owned()),
            (SyntaxKind::ElsifKw, "elsif".to_owned()),
            (SyntaxKind::ElseKw, "else".to_owned()),
        ]
    );
    assert!(
        !if_expression
            .descendants()
            .any(|node| node.kind() == SyntaxKind::ColonApplicationTail)
    );

    let (green, _) = run("if /*after-if*/ x /*after-condition*/ : a");
    let root = SyntaxNode::new_root(green);
    let arm = root
        .descendants()
        .find(|node| node.kind() == SyntaxKind::IfArm)
        .expect("if arm");
    let condition = arm
        .children()
        .find(|node| node.kind() == SyntaxKind::Condition)
        .expect("condition");
    assert_eq!(
        condition
            .children()
            .map(|node| node.kind())
            .collect::<Vec<_>>(),
        [SyntaxKind::OperatorChain]
    );
    assert_eq!(
        condition
            .descendants_with_tokens()
            .filter_map(|element| element.into_token())
            .filter(|token| token.kind() == SyntaxKind::BlockComment)
            .count(),
        0
    );
    assert_eq!(
        arm.children_with_tokens()
            .filter_map(|element| element.into_token())
            .filter(|token| token.kind() == SyntaxKind::BlockComment)
            .count(),
        2
    );
}

#[test]
fn if_c6_prioritizes_exact_nud_keyword_and_keeps_if_suffixes_whole() {
    let if_operator = OperatorTable::from_declarations([
        OperatorDeclaration::new(
            "if",
            OperatorFixities::new().with_prefix(BindingPower::scalar(40)),
        ),
        OperatorDeclaration::new(
            "elsif",
            OperatorFixities::new().with_infix(BindingPower::scalar(40), BindingPower::scalar(40)),
        ),
        OperatorDeclaration::new(
            "else",
            OperatorFixities::new().with_infix(BindingPower::scalar(40), BindingPower::scalar(40)),
        ),
    ])
    .expect("contextual if test table");
    let (green, exit) = run_with("if x: y", &if_operator);
    assert_eq!(green.to_string(), "if x: y");
    assert!(matches!(exit, Some(Err(Either::Right(_)))));
    assert!(
        SyntaxNode::new_root(green)
            .descendants()
            .any(|node| node.kind() == SyntaxKind::IfExpression)
    );

    for source in ["ifx", "if?", "if!"] {
        let (green, _) = run_with(source, &if_operator);
        assert!(
            !SyntaxNode::new_root(green)
                .descendants()
                .any(|node| node.kind() == SyntaxKind::IfExpression),
            "{source:?}"
        );
    }

    let (green, exit) = run_with("if x: a elsif y: b else: c", &if_operator);
    assert_eq!(green.to_string(), "if x: a elsif y: b else: c");
    assert!(matches!(exit, Some(Err(Either::Right(_)))));
    assert_eq!(
        SyntaxNode::new_root(green)
            .descendants()
            .filter(|node| node.kind() == SyntaxKind::IfArm)
            .count(),
        2
    );

    for source in ["if x: a elsif! b", "if x: a else? b"] {
        let (green, _) = run_with(source, &if_operator);
        let if_expression = SyntaxNode::new_root(green)
            .descendants()
            .find(|node| node.kind() == SyntaxKind::IfExpression)
            .expect("initial if remains accepted");
        assert_eq!(
            if_expression
                .children()
                .filter(|node| matches!(node.kind(), SyntaxKind::IfArm | SyntaxKind::ElseArm))
                .count(),
            1,
            "{source:?}"
        );
    }
}

#[test]
fn if_c6_keeps_condition_colon_and_inline_comma_with_their_owners() {
    let (green, exit) = run("(if (x: y): a, b)");
    assert_eq!(green.to_string(), "(if (x: y): a, b)");
    assert!(matches!(exit, Some(Err(Either::Right(_)))));

    let root = SyntaxNode::new_root(green);
    let if_expression = root
        .descendants()
        .find(|node| node.kind() == SyntaxKind::IfExpression)
        .expect("if primary");
    let arm = if_expression
        .children()
        .find(|node| node.kind() == SyntaxKind::IfArm)
        .expect("if arm");
    assert!(
        arm.children()
            .any(|node| node.kind() == SyntaxKind::Condition)
    );
    assert_eq!(
        arm.descendants_with_tokens()
            .filter_map(|element| element.into_token())
            .filter(|token| token.kind() == SyntaxKind::Comma)
            .count(),
        0
    );
    assert_eq!(
        root.descendants_with_tokens()
            .filter_map(|element| element.into_token())
            .filter(|token| token.kind() == SyntaxKind::Comma)
            .count(),
        1
    );
    assert!(
        arm.descendants()
            .any(|node| node.kind() == SyntaxKind::ColonApplicationTail)
    );
}

#[test]
fn if_c6_never_treats_path_separator_as_the_condition_colon_stop() {
    let operators = OperatorTable::from_declarations([OperatorDeclaration::new(
        "+",
        OperatorFixities::new()
            .with_infix(BindingPower::scalar(40), BindingPower::scalar(40))
            .with_suffix(BindingPower::scalar(80)),
    )])
    .expect("condition-stop operator table");
    assert_eq!(
        scan_dynamic_operator("+::T", &operators, OperatorSite::Led),
        scan_dynamic_operator_with_stops("+::T", &operators, OperatorSite::Led, STOP_COLON)
    );
}

#[test]
fn if_c6_reuses_indented_block_and_stops_at_companion_words() {
    let source = "if x:\n  a\n  b\nelse: c";
    let (green, exit) = run(source);
    assert_eq!(green.to_string(), source);
    assert!(matches!(exit, Some(Err(Either::Right(_)))));

    let root = SyntaxNode::new_root(green);
    let if_expression = root
        .descendants()
        .find(|node| node.kind() == SyntaxKind::IfExpression)
        .expect("if primary");
    assert_eq!(
        if_expression
            .descendants()
            .filter(|node| node.kind() == SyntaxKind::IndentedStatementBlock)
            .count(),
        1
    );
    assert_eq!(
        if_expression
            .descendants()
            .filter(|node| node.kind() == SyntaxKind::Statement)
            .count(),
        2
    );
    assert_eq!(
        if_expression
            .children()
            .filter(|node| node.kind() == SyntaxKind::ElseArm)
            .count(),
        1
    );
    assert!(
        !if_expression
            .descendants()
            .any(|node| node.kind() == SyntaxKind::Error)
    );

    for source in ["if x: a elsif y: b", "if x: a\n  elsif y: b"] {
        let (green, exit) = run(source);
        assert_eq!(green.to_string(), source, "{source:?}");
        assert!(matches!(exit, Some(Err(Either::Right(_)))), "{source:?}");
        assert_eq!(
            SyntaxNode::new_root(green)
                .descendants()
                .filter(|node| node.kind() == SyntaxKind::IfArm)
                .count(),
            2,
            "{source:?}"
        );
    }
}

#[test]
fn if_c6_keeps_non_companion_and_shallow_newline_outward() {
    for source in ["if x: a\nnext", "if x:\nnext", "if x { body }"] {
        let (green, exit) = run(source);
        assert!(matches!(exit, Some(Err(Either::Left(_)))), "{source:?}");
        assert!(
            green.to_string().starts_with("if x"),
            "{source:?}: {:?}",
            green.to_string()
        );
    }
}

#[test]
fn if_c6_recovers_accepted_arm_slots_once() {
    for (source, missing, error) in [
        ("if", 1, 0),
        ("if x", 1, 0),
        ("if x:", 1, 0),
        ("if : y", 1, 0),
        ("if x: @ y", 0, 1),
        ("if x: a else", 1, 0),
    ] {
        let (green, _) = run(source);
        assert_eq!(green.to_string(), source, "{source:?}");
        let root = SyntaxNode::new_root(green);
        assert_eq!(
            root.descendants()
                .filter(|node| node.kind() == SyntaxKind::Missing)
                .count(),
            missing,
            "{source:?}"
        );
        assert_eq!(
            root.descendants()
                .filter(|node| node.kind() == SyntaxKind::Error)
                .count(),
            error,
            "{source:?}"
        );
    }

    let (green, exit) = run("if x:\nnext");
    assert_eq!(green.to_string(), "if x:");
    assert!(matches!(exit, Some(Err(Either::Left(_)))));
    assert_eq!(
        SyntaxNode::new_root(green)
            .descendants()
            .filter(|node| node.kind() == SyntaxKind::Missing)
            .count(),
        1
    );
}

#[test]
fn if_c6_keeps_bare_else_if_nested_and_resumes_the_outer_chain() {
    let (green, exit) = run("if x: a else if y: b");
    assert_eq!(green.to_string(), "if x: a else if y: b");
    assert!(matches!(exit, Some(Err(Either::Right(_)))));
    let root = SyntaxNode::new_root(green);
    assert_eq!(
        root.descendants()
            .filter(|node| node.kind() == SyntaxKind::IfExpression)
            .count(),
        2
    );

    let (green, _) = run("if x: a else: b else: c");
    let if_expression = SyntaxNode::new_root(green)
        .descendants()
        .find(|node| node.kind() == SyntaxKind::IfExpression)
        .expect("initial if");
    assert_eq!(
        if_expression
            .children()
            .filter(|node| node.kind() == SyntaxKind::ElseArm)
            .count(),
        1
    );

    let operators = dynamic_operator_table();
    let (green, exit) = run_with("(if x: a else: b) + c", &operators);
    assert_eq!(green.to_string(), "(if x: a else: b) + c");
    assert!(matches!(exit, Some(Err(Either::Right(_)))));
    assert_eq!(
        operator_chain_children(&green),
        [
            SyntaxKind::ParenthesizedExpression,
            SyntaxKind::InfixOperatorUse,
            SyntaxKind::IdentifierExpression,
        ]
    );
}
