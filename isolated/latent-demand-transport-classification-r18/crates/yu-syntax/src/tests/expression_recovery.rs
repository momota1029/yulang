use crate::tests::support::*;
use crate::{
    ambient_claim::AmbientClaimView, handoff::MlMode, statement::StatementLineHandoff,
    structural_diagnostic::StructuralKind,
};

fn direct_required_expr_with_facts<'source>(
    source: &'source str,
    stops: Stops,
) -> (GreenNode, NormalizedExit, &'source str, Vec<StructuralFact>) {
    let operators = OperatorTable::empty();
    let mut input = source;
    let mut recover = Recover::new_for_test(&operators);
    let mut output = GreenNodeBuilder::new();
    output.start_node(SyntaxKind::Root.into());
    output.start_node(SyntaxKind::OperatorChain.into());
    let (item, origin, line) = crate::lexical::expression_item::expression_item(
        crate::cursor::SyntaxIn::new(&mut input, &mut recover, &mut output),
        OperatorSite::Nud,
        0,
        LineEntry::InLine,
        None,
        0,
        stops,
    );
    let exit = crate::expression::required_expr_item_normalized(
        crate::cursor::SyntaxIn::new(&mut input, &mut recover, &mut output),
        item,
        None,
        0,
        stops,
        MlMode::All,
        StatementLineHandoff::OrdinaryLayout,
        origin,
        line,
        None,
        Some(AmbientClaimView::root_statement(0)).into(),
        None,
    );
    output.finish_node();
    output.finish_node();
    let green = finish_with_discarded_recoveries(output, recover);
    let facts = structural_facts(&green);
    (green, exit, input, facts)
}

fn expression_with_facts(
    source: &str,
    operators: &OperatorTable,
) -> (GreenNode, Option<NormalizedExit>, Vec<StructuralFact>) {
    let mut input = source;
    let mut recover = Recover::new_for_test(operators);
    let mut output = GreenNodeBuilder::new();
    output.start_node(SyntaxKind::Root.into());
    let mut exit = expr_normalized(
        crate::cursor::SyntaxIn::new(&mut input, &mut recover, &mut output),
        None,
        0,
        0,
        MlMode::All,
        StatementLineHandoff::OrdinaryLayout,
        0,
        LineEntry::InLine,
        None,
        Some(AmbientClaimView::root_statement(0)).into(),
        None,
    );
    if let Some(NormalizedExit::Complete(Err(Either::Right(end)), _)) = &mut exit {
        emit_end(&mut output, end);
    }
    output.finish_node();
    let green = finish_with_discarded_recoveries(output, recover);
    let facts = structural_facts(&green);
    (green, exit, facts)
}

fn statement_with_facts(source: &str) -> (GreenNode, NormalizedExit, Vec<StructuralFact>) {
    let operators = OperatorTable::empty();
    let mut input = source;
    let mut recover = Recover::new_for_test(&operators);
    let mut output = GreenNodeBuilder::new();
    output.start_node(SyntaxKind::Root.into());
    let mut exit = crate::statement::statement_normalized(
        crate::cursor::SyntaxIn::new(&mut input, &mut recover, &mut output),
        0,
        0,
        0,
        LineEntry::InLine,
        None,
        Some(AmbientClaimView::root_statement(0)).into(),
        Some(crate::sequence::SequenceOwner::RootStatement),
    );
    if let NormalizedExit::Complete(Err(Either::Right(end)), _) = &mut exit {
        emit_end(&mut output, end);
    }
    output.finish_node();
    let green = finish_with_discarded_recoveries(output, recover);
    let facts = structural_facts(&green);
    (green, exit, facts)
}

#[test]
fn required_operand_unclaimed_close_publishes_missing_and_keeps_its_whole_item() {
    let operators = OperatorTable::from_declarations([OperatorDeclaration::new(
        "?",
        OperatorFixities::new().with_prefix(BindingPower::scalar(70)),
    )])
    .unwrap();
    let mut recover = Recover::new_for_test(&operators);
    let mut input = "? ]";
    let mut output = GreenNodeBuilder::new();
    output.start_node(SyntaxKind::Root.into());
    let rejected = expr_normalized(
        crate::cursor::SyntaxIn::new(&mut input, &mut recover, &mut output),
        None,
        0,
        0,
        MlMode::All,
        StatementLineHandoff::OrdinaryLayout,
        0,
        LineEntry::InLine,
        None,
        Some(AmbientClaimView::root_statement(0)).into(),
        None,
    );
    assert!(rejected.is_none());
    assert_eq!(input, "? ]");

    let mut input = " ]";
    output.start_node(SyntaxKind::OperatorChain.into());
    let (item, origin, line) = crate::lexical::expression_item::expression_item(
        crate::cursor::SyntaxIn::new(&mut input, &mut recover, &mut output),
        OperatorSite::Nud,
        0,
        LineEntry::InLine,
        None,
        0,
        0,
    );
    let exit = crate::expression::required_expr_item_normalized(
        crate::cursor::SyntaxIn::new(&mut input, &mut recover, &mut output),
        item,
        None,
        0,
        0,
        MlMode::All,
        StatementLineHandoff::OrdinaryLayout,
        origin,
        line,
        None,
        Some(AmbientClaimView::root_statement(0)).into(),
        None,
    );
    output.finish_node();
    output.finish_node();
    let green = finish_with_discarded_recoveries(output, recover);
    assert_eq!(green.to_string(), "");
    assert_eq!(structural_facts(&green), [(StructuralKind::Missing, 0..0)]);
    let NormalizedExit::Complete(Err(Either::Left(item)), LineEntry::InLine) = exit else {
        panic!("the same bracket must remain pending")
    };
    assert_eq!(token_kind(&item), Some(TokenKind::RBracket));
    assert_eq!(item.extent(origin).recovery_range(), 0..2);
    assert_eq!(input, "");
}

#[test]
fn required_operand_boundaries_keep_items_except_ordinary_eof_leading() {
    for (source, stops, expected_green, range) in [
        ("", 0, "", 0..0),
        (" ", 0, " ", 1..1),
        (",", crate::lexical::stops::STOP_COMMA, "", 0..0),
        ("]", 0, "", 0..0),
        ("[", 0, "", 0..0),
        ("\r\n", crate::lexical::stops::STOP_LINE_BREAK, "", 0..0),
    ] {
        let (green, exit, remainder, facts) = direct_required_expr_with_facts(source, stops);
        assert_eq!(green.to_string(), expected_green, "{source:?}");
        assert_eq!(facts, [(StructuralKind::Missing, range)], "{source:?}");
        assert!(
            matches!(exit, NormalizedExit::Complete(Err(_), _)),
            "{source:?}"
        );
        assert_eq!(remainder, "", "{source:?}");
    }
}

#[test]
fn required_operand_error_run_retries_from_its_structural_error_group() {
    let (green, exit, remainder, facts) = direct_required_expr_with_facts("@ x", 0);
    assert_eq!(green.to_string(), "@ x");
    assert!(matches!(
        exit,
        NormalizedExit::Complete(Err(Either::Right(_)), _)
    ));
    assert_eq!(remainder, "");
    assert_eq!(facts, [(StructuralKind::ErrorGroup, 0..1)]);
    let root = SyntaxNode::new_root(green.clone());
    let chain = root.first_child().unwrap();
    assert_eq!(chain.kind(), SyntaxKind::OperatorChain);
    let children = chain.children_with_tokens().collect::<Vec<_>>();
    assert_eq!(children[0].as_token().unwrap().kind(), SyntaxKind::Error);
    assert_eq!(children[0].to_string(), "@");
    assert_eq!(children[1].kind(), SyntaxKind::IdentifierExpression);
    assert_eq!(children[1].to_string(), " x");
    let retry = children[1]
        .as_node()
        .unwrap()
        .children_with_tokens()
        .collect::<Vec<_>>();
    assert_eq!(retry[0].kind(), SyntaxKind::Whitespace);
    assert_eq!(retry[0].to_string(), " ");
    assert_eq!(retry[1].kind(), SyntaxKind::Identifier);
    assert_eq!(retry[1].to_string(), "x");
    assert_eq!(retry.len(), 2);
    assert_eq!(children.len(), 2);

    let (_, boundary_exit, boundary_remainder, boundary_facts) =
        direct_required_expr_with_facts("@ ,", crate::lexical::stops::STOP_COMMA);
    assert_eq!(boundary_facts, [(StructuralKind::ErrorGroup, 0..1)]);
    assert!(matches!(
        boundary_exit,
        NormalizedExit::Complete(Err(Either::Left(_)), _)
    ));
    assert_eq!(boundary_remainder, "");

    let operators = OperatorTable::from_declarations([OperatorDeclaration::new(
        "+",
        OperatorFixities::new().with_infix(BindingPower::scalar(50), BindingPower::scalar(50)),
    )])
    .unwrap();
    let (_, _, infix_facts) = expression_with_facts("a + @ b", &operators);
    assert_eq!(infix_facts, [(StructuralKind::ErrorGroup, 4..5)]);
}

#[test]
fn required_for_inline_body_missing_and_error_are_structural_facts() {
    for (source, kind, range, emitted) in [
        (" ]", StructuralKind::Missing, 0..0, ""),
        (" @", StructuralKind::ErrorGroup, 1..2, " @"),
    ] {
        let (green, exit, remainder, facts) = direct_required_expr_with_facts(source, 0);
        assert_eq!(facts, [(kind, range)]);
        assert_eq!(green.to_string(), emitted);
        assert_eq!(remainder, "");
        if kind == StructuralKind::Missing {
            let NormalizedExit::Complete(Err(Either::Left(item)), LineEntry::InLine) = exit else {
                panic!("the protected close must remain pending")
            };
            assert_eq!(token_kind(&item), Some(TokenKind::RBracket));
            assert_eq!(item.extent(source.len()).recovery_range(), 0..2);
        }
    }
}

#[test]
fn actual_for_inline_body_missing_and_error_preserve_cst_and_handoff() {
    for (source, kind, range, emitted) in [
        (
            "for x in xs: ]",
            StructuralKind::Missing,
            13..13,
            "for x in xs: ",
        ),
        (
            "for x in xs: @",
            StructuralKind::ErrorGroup,
            13..14,
            "for x in xs: @",
        ),
    ] {
        let (green, exit, facts) = statement_with_facts(source);
        assert_eq!(green.to_string(), emitted);
        assert_eq!(facts, [(kind, range.clone())]);
        let root = SyntaxNode::new_root(green.clone());
        let expected_body = match kind {
            StructuralKind::Missing => "        Missing@13..13\n",
            StructuralKind::ErrorGroup => "        Error@13..14 \"@\"\n",
            StructuralKind::Invalid => unreachable!("inline-body witness has no Invalid CST node"),
        };
        assert_eq!(
            format!("{root:#?}"),
            format!(
                concat!(
                    "Root@0..{end}\n",
                    "  Statement@0..{end}\n",
                    "    ForStatement@0..{end}\n",
                    "      ForKw@0..3 \"for\"\n",
                    "      Whitespace@3..4 \" \"\n",
                    "      Pattern@4..5\n",
                    "        IdentifierPattern@4..5\n",
                    "          Identifier@4..5 \"x\"\n",
                    "      Whitespace@5..6 \" \"\n",
                    "      InKw@6..8 \"in\"\n",
                    "      Whitespace@8..9 \" \"\n",
                    "      ForIterable@9..11\n",
                    "        OperatorChain@9..11\n",
                    "          IdentifierExpression@9..11\n",
                    "            Identifier@9..11 \"xs\"\n",
                    "      Colon@11..12 \":\"\n",
                    "      Whitespace@12..13 \" \"\n",
                    "      OperatorChain@13..{end}\n",
                    "{expected_body}",
                ),
                end = range.end,
                expected_body = expected_body,
            )
        );
        let recovery_kind = match kind {
            StructuralKind::Missing => SyntaxKind::Missing,
            StructuralKind::ErrorGroup => SyntaxKind::Error,
            StructuralKind::Invalid => unreachable!("inline-body witness has no Invalid CST node"),
        };
        let recovery_elements: Vec<_> = root
            .descendants_with_tokens()
            .filter(|node| matches!(node.kind(), SyntaxKind::Missing | SyntaxKind::Error))
            .collect();
        assert_eq!(recovery_elements.len(), 1);
        let recovery = &recovery_elements[0];
        assert_eq!(
            recovery.as_token().is_some(),
            kind == StructuralKind::ErrorGroup
        );
        assert_eq!(recovery.kind(), recovery_kind);
        assert_eq!(usize::from(recovery.text_range().start()), range.start);
        assert_eq!(usize::from(recovery.text_range().end()), range.end);
        let chain = recovery.parent().expect("inline body chain");
        assert_eq!(chain.kind(), SyntaxKind::OperatorChain);
        assert_eq!(chain.parent().unwrap().kind(), SyntaxKind::ForStatement);
        match kind {
            StructuralKind::Missing => {
                let NormalizedExit::Complete(Err(Either::Left(item)), _) = &exit else {
                    panic!("the body close must remain pending")
                };
                assert_eq!(token_kind(item), Some(TokenKind::RBracket));
                assert_eq!(recovery.to_string(), "");
            }
            StructuralKind::ErrorGroup => {
                assert!(matches!(
                    exit,
                    NormalizedExit::Complete(Err(Either::Right(_)), _)
                ));
                assert_eq!(recovery.to_string(), "@");
            }
            StructuralKind::Invalid => unreachable!("inline-body witness has no Invalid CST node"),
        }
        let item = match &exit {
            NormalizedExit::Complete(Err(Either::Left(item)), LineEntry::InLine)
                if kind == StructuralKind::Missing =>
            {
                item
            }
            NormalizedExit::Complete(Err(Either::Right(end)), LineEntry::InLine)
                if kind == StructuralKind::ErrorGroup =>
            {
                assert!(end.item.payload_view().is_eof());
                &end.item
            }
            _ => panic!("inline bodies must preserve the InLine handoff"),
        };
        let extent = item.extent(source.len());
        match kind {
            StructuralKind::Missing => {
                assert_eq!(extent.physical(), 12..14);
                assert_eq!(extent.leading(), 12..13);
                assert_eq!(extent.remaining(), 13..13);
                assert_eq!(extent.payload(), 13..14);
                assert_eq!(extent.recovery_range(), 13..14);
            }
            StructuralKind::ErrorGroup => {
                assert_eq!(extent.physical(), 14..14);
                assert_eq!(extent.leading(), 14..14);
                assert_eq!(extent.remaining(), 14..14);
                assert_eq!(extent.payload(), 14..14);
                assert_eq!(extent.recovery_range(), 14..14);
            }
            StructuralKind::Invalid => unreachable!("inline-body witness has no Invalid CST node"),
        }
    }
}

#[test]
fn required_operand_callers_publish_structural_facts() {
    let operators = OperatorTable::empty();
    for (source, expected) in [
        ("if : x", (StructuralKind::Missing, 3..3)),
        ("case : _ -> x", (StructuralKind::Missing, 4..4)),
        ("case x: _ if -> y", (StructuralKind::Missing, 13..13)),
    ] {
        let (_, _, facts) = expression_with_facts(source, &operators);
        assert_eq!(facts, [expected], "{source:?}");
    }

    let (_, _, iterable_facts) = statement_with_facts("for x in ]");
    assert_eq!(iterable_facts, [(StructuralKind::Missing, 9..9)]);

    let (_, _, body_facts) = statement_with_facts("for x in xs: @");
    assert_eq!(body_facts, [(StructuralKind::ErrorGroup, 13..14)]);
}

fn direct_child(node: &SyntaxNode, kind: SyntaxKind) -> SyntaxNode {
    node.children()
        .find(|child| child.kind() == kind)
        .unwrap_or_else(|| panic!("{kind:?} direct child of {:#?}", node.kind()))
}

fn direct_missing_in_required_chain(slot: &SyntaxNode) -> SyntaxNode {
    let chain = direct_child(slot, SyntaxKind::OperatorChain);
    let missing = direct_child(&chain, SyntaxKind::Missing);
    assert_eq!(missing.text_range(), chain.text_range());
    missing
}

#[test]
fn required_operand_cst_slots_select_initial_callers() {
    for (source, slot) in [
        ("if : x", SyntaxKind::Condition),
        ("case : _ -> x", SyntaxKind::CaseScrutinee),
        ("catch : _ -> x", SyntaxKind::CatchScrutinee),
        ("case x: _ if -> y", SyntaxKind::CaseGuard),
        ("catch x: _ if -> y", SyntaxKind::CatchGuard),
        ("for x in ]", SyntaxKind::ForIterable),
        ("for x in\n]", SyntaxKind::ForIterable),
    ] {
        let (green, _, _) = run_statement_normalized(source, 0, LineEntry::InLine, None);
        let root = SyntaxNode::new_root(green);
        let owner = root.descendants().find(|node| node.kind() == slot).unwrap();
        let missing = direct_missing_in_required_chain(&owner);
        assert_eq!(
            usize::from(missing.text_range().start()),
            owner.text_range().end().into()
        );
    }

    let (green, _, _) = run_statement_normalized(
        "for x in\r\n> > ```\nouter",
        0,
        LineEntry::InLine,
        Some(&FenceBoundary {
            opener: crate::lexical::yumark::FenceOpener {
                line: 0,
                marker: 0..3,
                marker_width: 3,
            },
            prefix_policy: crate::lexical::yumark::FencePrefixPolicy::ActivePrefixQuote {
                depth: 2,
                base: 0,
            },
            close_column: 0,
        }),
    );
    let root = SyntaxNode::new_root(green);
    let iterable = root
        .descendants()
        .find(|node| node.kind() == SyntaxKind::ForIterable)
        .unwrap();
    assert_eq!(
        direct_missing_in_required_chain(&iterable).text_range(),
        rowan::TextRange::new(8.into(), 8.into())
    );
}

#[test]
fn required_operand_cst_keeps_nested_nud_and_terminal_recovery_distinct() {
    let operators = OperatorTable::from_declarations([
        OperatorDeclaration::new(
            "?",
            OperatorFixities::new().with_prefix(BindingPower::scalar(70)),
        ),
        OperatorDeclaration::new(
            "+",
            OperatorFixities::new().with_infix(BindingPower::scalar(50), BindingPower::scalar(50)),
        ),
    ])
    .unwrap();
    for (source, operator) in [
        ("? @ x", SyntaxKind::PrefixOperatorUse),
        ("a + @ x", SyntaxKind::InfixOperatorUse),
    ] {
        let (green, _, _) = expression_with_facts(source, &operators);
        let root = SyntaxNode::new_root(green);
        let chain = direct_child(&root, SyntaxKind::OperatorChain);
        let children = chain.children_with_tokens().collect::<Vec<_>>();
        assert!(children.iter().any(|child| child.kind() == operator));
        let error = children
            .iter()
            .position(|child| child.kind() == SyntaxKind::Error)
            .unwrap();
        let retry = children
            .iter()
            .enumerate()
            .skip(error + 1)
            .find_map(|(index, child)| {
                (child.kind() == SyntaxKind::IdentifierExpression).then_some(index)
            })
            .unwrap();
        assert!(error < retry);
        let retry = children[retry].as_node().unwrap();
        assert_eq!(retry.parent().unwrap().kind(), SyntaxKind::OperatorChain);
    }

    for source in ["]", "@ x", "@\r\n界"] {
        let (green, _, _, _) = direct_required_expr_with_facts(source, 0);
        let root = SyntaxNode::new_root(green);
        let chain = direct_child(&root, SyntaxKind::OperatorChain);
        if source == "]" {
            assert_eq!(
                direct_child(&chain, SyntaxKind::Missing).text_range(),
                rowan::TextRange::new(0.into(), 0.into())
            );
        } else {
            let elements = chain.children_with_tokens().collect::<Vec<_>>();
            let error = elements
                .iter()
                .find(|child| child.kind() == SyntaxKind::Error)
                .unwrap();
            assert_eq!(
                error.text_range(),
                rowan::TextRange::new(0.into(), 1.into())
            );
            assert!(
                elements
                    .iter()
                    .any(|child| child.kind() == SyntaxKind::IdentifierExpression)
            );
        }
    }
}

#[test]
fn required_operand_cst_orders_caller_and_nested_nud_recovery_in_one_chain() {
    let operators = OperatorTable::from_declarations([
        OperatorDeclaration::new(
            "?",
            OperatorFixities::new().with_prefix(BindingPower::scalar(70)),
        ),
        OperatorDeclaration::new(
            "+",
            OperatorFixities::new().with_infix(BindingPower::scalar(50), BindingPower::scalar(50)),
        ),
    ])
    .unwrap();
    for (source, accepted, nested_kind) in [
        (
            "if @ ? [: x",
            SyntaxKind::PrefixOperatorUse,
            SyntaxKind::Missing,
        ),
        (
            "if @ a + @ x: y",
            SyntaxKind::InfixOperatorUse,
            SyntaxKind::Error,
        ),
    ] {
        let (green, _, _) = expression_with_facts(source, &operators);
        let root = SyntaxNode::new_root(green);
        let condition = root
            .descendants()
            .find(|node| node.kind() == SyntaxKind::Condition)
            .unwrap();
        let chain = direct_child(&condition, SyntaxKind::OperatorChain);
        let elements = chain.children_with_tokens().collect::<Vec<_>>();
        let caller_error = elements
            .iter()
            .position(|child| child.kind() == SyntaxKind::Error)
            .unwrap();
        let accepted = elements
            .iter()
            .position(|child| child.kind() == accepted)
            .unwrap();
        let nested = elements
            .iter()
            .enumerate()
            .skip(accepted + 1)
            .find_map(|(index, child)| (child.kind() == nested_kind).then_some(index))
            .unwrap();
        assert!(caller_error < accepted && accepted < nested, "{source:?}");
        assert_eq!(
            elements
                .iter()
                .filter(|child| child.kind() == SyntaxKind::Missing)
                .count(),
            usize::from(nested_kind == SyntaxKind::Missing)
        );
    }

    let (green, _, _, _) = direct_required_expr_with_facts("@", 0);
    let root = SyntaxNode::new_root(green);
    let chain = direct_child(&root, SyntaxKind::OperatorChain);
    assert!(
        chain
            .children_with_tokens()
            .any(|child| child.kind() == SyntaxKind::Error)
    );
    assert!(
        !chain
            .children_with_tokens()
            .any(|child| child.kind() == SyntaxKind::Missing)
    );
}

#[test]
fn required_operand_cst_selects_post_infix_missing_from_ordered_children() {
    let source = "a +";
    let operators = OperatorTable::from_declarations([OperatorDeclaration::new(
        "+",
        OperatorFixities::new().with_infix(BindingPower::scalar(50), BindingPower::scalar(50)),
    )])
    .unwrap();
    let (green, exit, facts) = expression_with_facts(source, &operators);
    assert_eq!(facts, [(StructuralKind::Missing, 3..3)]);
    let root = SyntaxNode::new_root(green);
    assert_eq!(root.kind(), SyntaxKind::Root);
    assert!(root.parent().is_none());
    assert_eq!(root.text_range(), rowan::TextRange::new(0.into(), 3.into()));
    assert_eq!(root.to_string(), source);
    let root_children = root.children_with_tokens().collect::<Vec<_>>();
    assert_eq!(root_children.len(), 1);
    let chain = root_children[0].as_node().unwrap();
    assert_eq!(chain.kind(), SyntaxKind::OperatorChain);
    assert_eq!(chain.parent(), Some(root.clone()));
    assert_eq!(chain.text_range(), root.text_range());
    assert_eq!(chain.to_string(), source);
    let children = chain.children_with_tokens().collect::<Vec<_>>();
    assert_eq!(children.len(), 3);
    for (child, kind, text, start, end) in [
        (&children[0], SyntaxKind::IdentifierExpression, "a", 0, 1),
        (&children[1], SyntaxKind::InfixOperatorUse, " +", 1, 3),
        (&children[2], SyntaxKind::Missing, "", 3, 3),
    ] {
        assert!(child.as_node().is_some());
        assert_eq!(child.parent(), Some(chain.clone()));
        assert_eq!(child.kind(), kind);
        assert_eq!(child.to_string(), text);
        assert_eq!(
            child.text_range(),
            rowan::TextRange::new(start.into(), end.into())
        );
    }
    let identifier = children[0].as_node().unwrap();
    let identifier_children = identifier.children_with_tokens().collect::<Vec<_>>();
    assert_eq!(identifier_children.len(), 1);
    let infix = children[1].as_node().unwrap();
    let infix_children = infix.children_with_tokens().collect::<Vec<_>>();
    assert_eq!(infix_children.len(), 2);
    for (child, parent, kind, text, start, end) in [
        (
            &identifier_children[0],
            identifier,
            SyntaxKind::Identifier,
            "a",
            0,
            1,
        ),
        (&infix_children[0], infix, SyntaxKind::Whitespace, " ", 1, 2),
        (&infix_children[1], infix, SyntaxKind::Operator, "+", 2, 3),
    ] {
        let token = child.as_token().unwrap();
        assert_eq!(token.parent(), Some(parent.clone()));
        assert_eq!(token.kind(), kind);
        assert_eq!(token.text(), text);
        assert_eq!(
            token.text_range(),
            rowan::TextRange::new(start.into(), end.into())
        );
    }
    let missing = children[2].as_node().unwrap();
    assert!(missing.children_with_tokens().next().is_none());
    assert_eq!(missing.prev_sibling_or_token(), Some(children[1].clone()));
    assert!(missing.next_sibling_or_token().is_none());
    let recoveries = root
        .descendants_with_tokens()
        .filter(|element| {
            matches!(
                element.kind(),
                SyntaxKind::Missing | SyntaxKind::Error | SyntaxKind::Invalid
            )
        })
        .collect::<Vec<_>>();
    assert_eq!(recoveries, vec![children[2].clone()]);
    assert!(
        !root
            .descendants_with_tokens()
            .any(|element| element.kind() == SyntaxKind::PrefixOperatorUse)
    );

    let Some(NormalizedExit::Complete(Err(Either::Right(end)), LineEntry::InLine)) = exit else {
        panic!("the missing infix operand must preserve ordinary EOF and InLine handoff")
    };
    assert!(end.item.payload_view().is_eof());
    let extent = end.item.extent(source.len());
    assert_eq!(extent.physical(), 3..3);
    assert_eq!(extent.leading(), 3..3);
    assert_eq!(extent.remaining(), 3..3);
    assert_eq!(extent.payload(), 3..3);
    assert_eq!(extent.recovery_range(), 3..3);
}
