use super::*;

fn expression(root: &SyntaxNode, kind: SyntaxKind) -> SyntaxNode {
    root.descendants()
        .find(|node| node.kind() == kind)
        .expect("case-like expression")
}

fn assert_handoff_identifier(exit: &Option<TailExit>, spelling: &str) {
    let Some(Err(Either::Left(item))) = exit else {
        panic!("expected an unconsumed identifier handoff");
    };
    assert_eq!(
        item.payload_view().token_kind(),
        Some(TokenKind::Identifier)
    );
    assert_eq!(item.payload_view().spelling(), Some(spelling));
    assert!(item.leading_view().has_ordinary_newline());
}

#[test]
fn case_like_c7_builds_the_family_specific_inline_topology() {
    let source = "case 'go value: 1 if ready -> yes, _ where fallback -> no,";
    let (green, exit) = run(source);
    assert_eq!(green.to_string(), source);
    assert!(matches!(exit, Some(Err(Either::Right(_)))));

    let root = SyntaxNode::new_root(green);
    let case = expression(&root, SyntaxKind::CaseExpression);
    assert_eq!(
        case.children().map(|node| node.kind()).collect::<Vec<_>>(),
        [
            SyntaxKind::CaseLabel,
            SyntaxKind::CaseScrutinee,
            SyntaxKind::CaseBlock,
        ]
    );
    assert_eq!(
        case.descendants()
            .filter(|node| node.kind() == SyntaxKind::CaseArm)
            .count(),
        2
    );
    assert_eq!(
        case.descendants()
            .filter(|node| node.kind() == SyntaxKind::CaseGuard)
            .count(),
        2
    );
    assert_eq!(
        case.descendants()
            .filter(|node| node.kind() == SyntaxKind::CaseArmSeparator)
            .count(),
        2
    );
    assert_eq!(
        case.descendants_with_tokens()
            .filter_map(|element| element.into_token())
            .filter(|token| token.kind() == SyntaxKind::Arrow)
            .count(),
        2
    );
    assert!(
        !case
            .descendants()
            .any(|node| node.kind() == SyntaxKind::ColonApplicationTail)
    );
}

#[test]
fn case_like_c7_keeps_catch_handler_and_braces_with_catch() {
    let source = "catch action { err, handler -> recover, _ -> fallback }";
    let (green, exit) = run(source);
    assert_eq!(green.to_string(), source);
    assert!(matches!(exit, Some(Err(Either::Right(_)))));

    let root = SyntaxNode::new_root(green);
    let catch = expression(&root, SyntaxKind::CatchExpression);
    let block = catch
        .children()
        .find(|node| node.kind() == SyntaxKind::CatchBlock)
        .expect("CatchBlock");
    assert_eq!(
        block
            .children_with_tokens()
            .filter_map(|element| element.into_token())
            .filter(|token| matches!(token.kind(), SyntaxKind::LBrace | SyntaxKind::RBrace))
            .count(),
        2
    );
    assert_eq!(
        block
            .children()
            .filter(|node| node.kind() == SyntaxKind::CatchArm)
            .count(),
        2
    );
    assert_eq!(
        block
            .descendants()
            .filter(|node| node.kind() == SyntaxKind::CatchArmSeparator)
            .count(),
        1
    );
    let first = block
        .children()
        .find(|node| node.kind() == SyntaxKind::CatchArm)
        .expect("first CatchArm");
    assert_eq!(
        first
            .children()
            .filter(|node| node.kind() == SyntaxKind::Pattern)
            .count(),
        2
    );
    assert!(
        !catch
            .descendants()
            .any(|node| node.kind() == SyntaxKind::BracedStatementBlockExpression)
    );
}

#[test]
fn case_like_c7_keeps_catch_colon_inline_single_and_recovers_required_slots() {
    let source = "catch action: err, handler -> recover";
    let (green, exit) = run(source);
    assert_eq!(green.to_string(), source);
    assert!(matches!(exit, Some(Err(Either::Right(_)))));
    let root = SyntaxNode::new_root(green);
    let catch = expression(&root, SyntaxKind::CatchExpression);
    assert_eq!(
        catch
            .descendants()
            .filter(|node| node.kind() == SyntaxKind::CatchArm)
            .count(),
        1
    );

    let source = "catch action { err -> recover";
    let (green, exit) = run(source);
    assert_eq!(green.to_string(), source);
    assert!(matches!(exit, Some(Err(Either::Right(_)))));
    let root = SyntaxNode::new_root(green);
    let block = root
        .descendants()
        .find(|node| node.kind() == SyntaxKind::CatchBlock)
        .expect("CatchBlock");
    assert_eq!(
        block
            .children()
            .filter(|node| node.kind() == SyntaxKind::Missing)
            .count(),
        1
    );
}

#[test]
fn case_like_c7_keeps_current_depth_brace_newlines_out_of_arm_bodies() {
    let source = "catch action { err -> recover\n  _ -> fallback }";
    let (green, exit) = run(source);
    assert_eq!(green.to_string(), source);
    assert!(matches!(exit, Some(Err(Either::Right(_)))));
    let root = SyntaxNode::new_root(green);
    let catch = expression(&root, SyntaxKind::CatchExpression);
    assert_eq!(
        catch
            .descendants()
            .filter(|node| node.kind() == SyntaxKind::CatchArm)
            .count(),
        2
    );
    assert!(
        !catch
            .descendants()
            .any(|node| node.kind() == SyntaxKind::MlArgument)
    );
}

#[test]
fn case_like_c7_reuses_introduced_body_layout_at_the_arrow_line() {
    let source = "case value:\n  1 ->\n    yes\n  _ -> no";
    let (green, exit) = run(source);
    assert_eq!(green.to_string(), source);
    assert!(matches!(exit, Some(Err(Either::Right(_)))));
    let root = SyntaxNode::new_root(green);
    let case = expression(&root, SyntaxKind::CaseExpression);
    assert_eq!(
        case.descendants()
            .filter(|node| node.kind() == SyntaxKind::CaseArm)
            .count(),
        2
    );
    assert_eq!(
        case.descendants()
            .filter(|node| node.kind() == SyntaxKind::IndentedStatementBlock)
            .count(),
        1
    );

    let source = "case value:\n  1 ->\n  _ -> no";
    let (green, exit) = run(source);
    assert_eq!(green.to_string(), source);
    assert!(matches!(exit, Some(Err(Either::Right(_)))));
    let root = SyntaxNode::new_root(green);
    let case = expression(&root, SyntaxKind::CaseExpression);
    assert_eq!(
        case.descendants()
            .filter(|node| node.kind() == SyntaxKind::CaseArm)
            .count(),
        2
    );
    assert_eq!(
        case.descendants()
            .filter(|node| node.kind() == SyntaxKind::IndentedStatementBlock)
            .count(),
        0
    );
}

#[test]
fn case_like_c7_keeps_pattern_and_guard_boundaries_exact() {
    for source in [
        "case x: :tag -> yes",
        "case x: (a, b) -> yes",
        "case x: n as if -> yes",
        "case x: n if cond -> yes",
        "case x: n where cond -> yes",
    ] {
        let (green, exit) = run(source);
        assert_eq!(green.to_string(), source, "{source:?}");
        assert!(matches!(exit, Some(Err(Either::Right(_)))), "{source:?}");
        let root = SyntaxNode::new_root(green);
        let case = expression(&root, SyntaxKind::CaseExpression);
        assert!(
            case.descendants()
                .any(|node| node.kind() == SyntaxKind::CaseArm),
            "{source:?}"
        );
    }

    let source = "case x: n ->> body";
    let (green, _) = run(source);
    let root = SyntaxNode::new_root(green);
    assert_eq!(
        root.descendants_with_tokens()
            .filter_map(|element| element.into_token())
            .filter(|token| token.kind() == SyntaxKind::Arrow)
            .count(),
        0
    );
    assert_eq!(
        root.descendants_with_tokens()
            .filter_map(|element| element.into_token())
            .filter(|token| token.kind() == SyntaxKind::Unknown)
            .map(|token| token.text().to_owned())
            .collect::<Vec<_>>(),
        ["->>"],
    );
}

#[test]
fn case_like_c7_returns_outer_delimiters_from_missing_arm_slots() {
    let source = "(case x: ->)";
    let (green, exit) = run(source);
    assert_eq!(green.to_string(), source);
    assert!(matches!(exit, Some(Err(Either::Right(_)))));
    let root = SyntaxNode::new_root(green);
    let case = expression(&root, SyntaxKind::CaseExpression);
    assert_eq!(
        case.descendants()
            .filter(|node| node.kind() == SyntaxKind::Missing)
            .count(),
        2
    );
    assert!(
        root.descendants_with_tokens()
            .filter_map(|element| element.into_token())
            .any(|token| token.kind() == SyntaxKind::RParen)
    );
}

#[test]
fn case_like_c7_prioritizes_exact_nud_keywords_and_preserves_case_brace_nonownership() {
    let operators = OperatorTable::from_declarations([
        OperatorDeclaration::new(
            "case",
            OperatorFixities::new().with_prefix(BindingPower::scalar(40)),
        ),
        OperatorDeclaration::new(
            "catch",
            OperatorFixities::new().with_prefix(BindingPower::scalar(40)),
        ),
    ])
    .expect("contextual case-like table");
    for source in ["case x: n -> yes", "catch x: n -> yes"] {
        let (green, _) = run_with(source, &operators);
        let root = SyntaxNode::new_root(green);
        assert!(
            root.descendants().any(|node| {
                matches!(
                    node.kind(),
                    SyntaxKind::CaseExpression | SyntaxKind::CatchExpression
                )
            }),
            "{source:?}"
        );
    }
    for source in ["casefold", "case?", "catcher", "catch!"] {
        let (green, _) = run_with(source, &operators);
        assert!(
            !SyntaxNode::new_root(green).descendants().any(|node| {
                matches!(
                    node.kind(),
                    SyntaxKind::CaseExpression | SyntaxKind::CatchExpression
                )
            }),
            "{source:?}"
        );
    }

    let (green, _) = run("case x { n -> yes }");
    let root = SyntaxNode::new_root(green);
    let block = root
        .descendants()
        .find(|node| node.kind() == SyntaxKind::CaseBlock)
        .expect("missing case block slot");
    assert!(
        !block
            .descendants_with_tokens()
            .filter_map(|element| element.into_token())
            .any(|token| token.kind() == SyntaxKind::LBrace)
    );
}

#[test]
fn case_like_c7_handoffs_wrong_colon_body_indentation() {
    for (source, block_kind, arm_kind) in [
        (
            "case x:\ny -> z",
            SyntaxKind::CaseBlock,
            SyntaxKind::CaseArm,
        ),
        (
            "catch x:\ny -> z",
            SyntaxKind::CatchBlock,
            SyntaxKind::CatchArm,
        ),
    ] {
        let (green, exit) = run(source);
        let root = SyntaxNode::new_root(green);
        let block = root
            .descendants()
            .find(|node| node.kind() == block_kind)
            .expect("case-like block");
        assert_eq!(
            block
                .descendants()
                .filter(|node| node.kind() == arm_kind)
                .count(),
            1,
            "{source:?}"
        );
        assert_eq!(
            block
                .descendants()
                .filter(|node| node.kind() == SyntaxKind::Missing)
                .count(),
            1,
            "{source:?}"
        );
        assert!(
            !block
                .descendants_with_tokens()
                .filter_map(|element| element.into_token())
                .any(|token| token.text() == "y"),
            "{source:?}"
        );
        assert_handoff_identifier(&exit, "y");
    }
}

#[test]
fn case_like_c7_keeps_arm_sequences_inside_their_layout_region() {
    for (source, expression_kind, arm_kind, successor) in [
        (
            "case x: a -> b\nc -> d",
            SyntaxKind::CaseExpression,
            SyntaxKind::CaseArm,
            "c",
        ),
        (
            "catch x: a -> b\nc -> d",
            SyntaxKind::CatchExpression,
            SyntaxKind::CatchArm,
            "c",
        ),
        (
            "case x:\n  a -> b\nc -> d",
            SyntaxKind::CaseExpression,
            SyntaxKind::CaseArm,
            "c",
        ),
        (
            "catch x:\n  a -> b\nc -> d",
            SyntaxKind::CatchExpression,
            SyntaxKind::CatchArm,
            "c",
        ),
    ] {
        let (green, exit) = run(source);
        let root = SyntaxNode::new_root(green);
        let expression = expression(&root, expression_kind);
        assert_eq!(
            expression
                .descendants()
                .filter(|node| node.kind() == arm_kind)
                .count(),
            1,
            "{source:?}"
        );
        assert_handoff_identifier(&exit, successor);
    }

    for (source, expression_kind, arm_kind, separator_kind) in [
        (
            "case x:\n  a -> b,\nc -> d",
            SyntaxKind::CaseExpression,
            SyntaxKind::CaseArm,
            SyntaxKind::CaseArmSeparator,
        ),
        (
            "catch x:\n  a -> b,\nc -> d",
            SyntaxKind::CatchExpression,
            SyntaxKind::CatchArm,
            SyntaxKind::CatchArmSeparator,
        ),
    ] {
        let (green, exit) = run(source);
        let root = SyntaxNode::new_root(green);
        let expression = expression(&root, expression_kind);
        assert_eq!(
            expression
                .descendants()
                .filter(|node| node.kind() == arm_kind)
                .count(),
            1,
            "{source:?}"
        );
        assert_eq!(
            expression
                .descendants()
                .filter(|node| node.kind() == separator_kind)
                .count(),
            1,
            "{source:?}"
        );
        assert_handoff_identifier(&exit, "c");
    }
}

#[test]
fn case_like_c7_recovers_case_next_arm_at_its_following_separator() {
    let source = "case x: a -> b, @, c -> d";
    let (green, exit) = run(source);
    assert_eq!(green.to_string(), source);
    assert!(matches!(exit, Some(Err(Either::Right(_)))));

    let root = SyntaxNode::new_root(green);
    let case = expression(&root, SyntaxKind::CaseExpression);
    assert_eq!(
        case.descendants()
            .filter(|node| node.kind() == SyntaxKind::CaseArm)
            .count(),
        3
    );
    assert_eq!(
        case.descendants()
            .filter(|node| node.kind() == SyntaxKind::CaseArmSeparator)
            .count(),
        2
    );
    assert!(case.descendants().any(|node| {
        node.kind() == SyntaxKind::Error
            && node
                .descendants_with_tokens()
                .filter_map(|element| element.into_token())
                .any(|token| token.text() == "@")
    }));
}

#[test]
fn case_like_c7_keeps_arm_entry_trivia_with_its_block() {
    let source = "case x:  a -> b,  _ -> c";
    let (green, exit) = run(source);
    assert_eq!(green.to_string(), source);
    assert!(matches!(exit, Some(Err(Either::Right(_)))));

    let root = SyntaxNode::new_root(green);
    let block = root
        .descendants()
        .find(|node| node.kind() == SyntaxKind::CaseBlock)
        .expect("CaseBlock");
    assert_eq!(
        block
            .children_with_tokens()
            .filter_map(|element| element.into_token())
            .filter(|token| token.kind() == SyntaxKind::Whitespace && token.text() == "  ")
            .count(),
        2
    );
}
