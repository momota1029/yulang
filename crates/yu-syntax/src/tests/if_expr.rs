use crate::tests::support::*;
use crate::{
    ExpectedSyntax, ambient_claim::AmbientClaimView, handoff::MlMode,
    statement::StatementLineHandoff, structural_diagnostic::StructuralKind,
};
use std::ops::Range;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum CstSlot {
    Body,
    BodyIntroducer,
    Condition,
    ElseBody,
}

fn parse_if_into<'s>(
    source: &'s str,
    origin: usize,
    stops: Stops,
    fence: Option<&FenceBoundary>,
    recover: &mut Recover,
    output: &mut GreenNodeBuilder,
) -> (NormalizedExit, &'s str) {
    let mut input = source;
    let exit = expr_normalized(
        crate::cursor::SyntaxIn::new(&mut input, recover, output),
        None,
        0,
        stops,
        MlMode::All,
        StatementLineHandoff::OrdinaryLayout,
        origin,
        LineEntry::InLine,
        fence,
        Some(AmbientClaimView::root_statement(0)).into(),
        None,
    )
    .expect("accepted If NUD");
    (exit, input)
}

#[test]
fn if_direct_rowan_slots_preserve_occurrence_order_and_native_trivia() {
    use SyntaxKind::*;

    // Interpret only ordered Rowan children and ancestry. In particular, two
    // Missing occurrences at the same byte offset need not belong to one arm.
    for (source, expected) in [
        ("if", vec![("Condition", 0, Missing, 2..2)]),
        (
            "if :",
            vec![("Condition", 0, Missing, 3..3), ("Body", 0, Missing, 4..4)],
        ),
        ("if x", vec![("BodyIntroducer", 0, Missing, 4..4)]),
        ("if x:", vec![("Body", 0, Missing, 5..5)]),
        (
            "if x: a elsif y",
            vec![("BodyIntroducer", 1, Missing, 15..15)],
        ),
        ("if x: a elsif y:", vec![("Body", 1, Missing, 16..16)]),
        ("if x: a else", vec![("ElseBody", 1, Missing, 12..12)]),
        ("if x: a else:", vec![("ElseBody", 1, Missing, 13..13)]),
        ("if x:\n  ", vec![("IndentedStatement", 0, Missing, 8..8)]),
        (
            "if x: a elsif y:\n  ",
            vec![("IndentedStatement", 1, Missing, 19..19)],
        ),
        (
            "if x: a else:\n  ",
            vec![("IndentedStatement", 1, Missing, 16..16)],
        ),
        ("if x: @ @ y", vec![("Body", 0, Error, 6..9)]),
        ("if x: a elsif y: @ @ z", vec![("Body", 1, Error, 17..20)]),
        ("if x: a else @ @ y", vec![("ElseBody", 1, Error, 13..16)]),
        ("if x: a else: @ @ y", vec![("ElseBody", 1, Error, 14..17)]),
        (
            "if α:\r\n  @ @ y",
            vec![("IndentedStatement", 0, Error, 10..13)],
        ),
        (
            "if if:",
            vec![
                ("Condition", 1, Missing, 5..5),
                ("Body", 1, Missing, 6..6),
                ("BodyIntroducer", 0, Missing, 6..6),
            ],
        ),
        ("if x: a elsif y: b else: c", vec![]),
        ("if x:\n  a\nelse: b", vec![]),
    ] {
        let (green, exit) = run(source);
        assert_eq!(green.to_string(), source, "{source:?}");
        assert!(matches!(exit, Some(Err(Either::Right(_)))), "{source:?}");
        let root = SyntaxNode::new_root(green);
        let arms: Vec<_> = root
            .descendants()
            .filter(|node| matches!(node.kind(), IfArm | ElseArm))
            .collect();
        let mut actual = Vec::new();
        for element in root.descendants_with_tokens() {
            assert_ne!(element.kind(), Invalid, "{source:?}");
            if !matches!(element.kind(), Missing | Error) {
                continue;
            }
            let parent = element.parent().unwrap();
            let arm = parent
                .ancestors()
                .find(|node| matches!(node.kind(), IfArm | ElseArm))
                .unwrap();
            let ordinal = arms.iter().position(|candidate| *candidate == arm).unwrap();
            let children: Vec<_> = parent.children_with_tokens().collect();
            let index = children.iter().position(|child| *child == element).unwrap();
            let role = match parent.kind() {
                OperatorChain => {
                    assert_eq!(parent.parent().unwrap().kind(), Condition);
                    assert_eq!(parent.parent().unwrap().parent(), Some(arm.clone()));
                    "Condition"
                }
                IndentedStatementBlock => {
                    assert_eq!(parent.parent(), Some(arm.clone()));
                    assert_eq!(parent.prev_sibling_or_token().unwrap().kind(), Colon);
                    "IndentedStatement"
                }
                ElseArm => "ElseBody",
                IfArm => {
                    assert!(
                        children[..index]
                            .iter()
                            .any(|child| child.kind() == Condition)
                    );
                    if children[..index].iter().any(|child| child.kind() == Colon) {
                        "Body"
                    } else {
                        "BodyIntroducer"
                    }
                }
                other => panic!("unexpected recovery parent {other:?} for {source:?}"),
            };
            let range = element.text_range();
            if element.kind() == Missing {
                let missing = element.as_node().expect("Missing is a node");
                assert!(missing.children_with_tokens().next().is_none());
                assert!(range.is_empty());
            } else {
                assert!(element.as_token().is_some());
                assert!(!range.is_empty());
                if index > 0 && children[index - 1].kind() == Error {
                    assert_eq!(children[index - 1].text_range().end(), range.start());
                    continue;
                }
            }
            let end = if element.kind() == Error {
                children[index..]
                    .iter()
                    .take_while(|child| child.kind() == Error)
                    .last()
                    .unwrap()
                    .text_range()
                    .end()
            } else {
                range.end()
            };
            actual.push((
                role,
                ordinal,
                element.kind(),
                u32::from(range.start())..u32::from(end),
            ));
        }
        assert_eq!(actual, expected, "{source:?}");
        for arm in &arms {
            assert_eq!(arm.parent().unwrap().kind(), IfExpression);
            let keyword = arm.first_token().unwrap();
            assert_eq!(keyword.parent(), Some(arm.clone()));
            assert!(matches!(
                (arm.kind(), keyword.kind()),
                (IfArm, IfKw | ElsifKw) | (ElseArm, ElseKw)
            ));
        }
    }

    // Initial and retry spaces are native siblings; only internal run trivia
    // becomes Error. Exact direct children prove the maximal group boundary.
    let (green, _) = run("if x: @ @ y");
    let root = SyntaxNode::new_root(green);
    let arm = root
        .descendants()
        .find(|node| node.kind() == IfArm)
        .unwrap();
    let expected = [
        (IfKw, false, 0..2),
        (Whitespace, false, 2..3),
        (Condition, true, 3..4),
        (Colon, false, 4..5),
        (Whitespace, false, 5..6),
        (Error, false, 6..7),
        (Error, false, 7..8),
        (Error, false, 8..9),
        (Whitespace, false, 9..10),
        (OperatorChain, true, 10..11),
    ];
    let actual: Vec<_> = arm
        .children_with_tokens()
        .map(|child| {
            assert_eq!(child.parent(), Some(arm.clone()));
            (
                child.kind(),
                child.as_node().is_some(),
                u32::from(child.text_range().start())..u32::from(child.text_range().end()),
            )
        })
        .collect();
    assert_eq!(actual, expected);
}

#[test]
fn if_elsif_condition_missing_error_and_retry_use_ordered_rowan_children() {
    use SyntaxKind::*;

    fn children(
        node: &SyntaxNode,
        expected: &[(SyntaxKind, bool, Range<usize>, &str)],
    ) -> Vec<rowan::NodeOrToken<SyntaxNode, crate::SyntaxToken>> {
        let actual: Vec<_> = node.children_with_tokens().collect();
        assert_eq!(actual.len(), expected.len(), "{node:?}");
        for (child, (kind, is_node, range, text)) in actual.iter().zip(expected) {
            assert_eq!(child.parent(), Some(node.clone()));
            assert_eq!(child.kind(), *kind);
            assert_eq!(child.as_node().is_some(), *is_node);
            assert_eq!(
                usize::from(child.text_range().start())..usize::from(child.text_range().end()),
                *range
            );
            assert_eq!(child.to_string(), *text);
        }
        actual
    }

    for (payload, end, recovery_range) in
        [("", 14, 14..14), ("@ @", 17, 14..17), ("@ @ g", 19, 14..17)]
    {
        let source = format!("if x: a elsif {payload}: b");
        let (green, exit) = run(&source);
        assert_eq!(green.to_string(), source);
        assert!(matches!(exit, Some(Err(Either::Right(_)))));
        let root = SyntaxNode::new_root(green);
        assert_eq!(root.kind(), Root);
        assert!(root.parent().is_none());
        let root_children = children(&root, &[(OperatorChain, true, 0..source.len(), &source)]);
        let outer = root_children[0].as_node().unwrap();
        let outer_children = children(outer, &[(IfExpression, true, 0..source.len(), &source)]);
        let expression = outer_children[0].as_node().unwrap();
        assert_eq!(
            root.descendants()
                .filter(|node| node.kind() == IfExpression)
                .count(),
            1
        );
        let expression_children = children(
            expression,
            &[
                (IfArm, true, 0..7, "if x: a"),
                (Whitespace, false, 7..8, " "),
                (IfArm, true, 8..source.len(), &source[8..]),
            ],
        );
        let arms: Vec<_> = expression.children().collect();
        assert_eq!(arms.len(), 2);
        assert!(
            root.descendants()
                .all(|node| !matches!(node.kind(), ElseArm | PrefixOperatorUse | InfixOperatorUse))
        );
        let first = expression_children[0].as_node().unwrap();
        children(
            first,
            &[
                (IfKw, false, 0..2, "if"),
                (Whitespace, false, 2..3, " "),
                (Condition, true, 3..4, "x"),
                (Colon, false, 4..5, ":"),
                (Whitespace, false, 5..6, " "),
                (OperatorChain, true, 6..7, "a"),
            ],
        );
        let arm = expression_children[2].as_node().unwrap();
        assert_eq!(arms.iter().position(|candidate| candidate == arm), Some(1));
        let arm_children = children(
            arm,
            &[
                (ElsifKw, false, 8..13, "elsif"),
                (Whitespace, false, 13..14, " "),
                (Condition, true, 14..end, payload),
                (Colon, false, end..end + 1, ":"),
                (Whitespace, false, end + 1..end + 2, " "),
                (OperatorChain, true, end + 2..end + 3, "b"),
            ],
        );
        let condition = arm_children[2].as_node().unwrap();
        let condition_children = children(condition, &[(OperatorChain, true, 14..end, payload)]);
        let chain = condition_children[0].as_node().unwrap();
        let mut expected_recovery = if payload.is_empty() {
            vec![(Missing, true, 14..14, "")]
        } else {
            vec![
                (Error, false, 14..15, "@"),
                (Error, false, 15..16, " "),
                (Error, false, 16..17, "@"),
            ]
        };
        if end == 19 {
            expected_recovery.push((IdentifierExpression, true, 17..19, " g"));
        }
        let chain_children = children(chain, &expected_recovery);
        let first_recovery = &chain_children[0];
        let recovery = if first_recovery.kind() == Missing {
            assert!(
                first_recovery
                    .as_node()
                    .unwrap()
                    .children_with_tokens()
                    .next()
                    .is_none()
            );
            assert!(first_recovery.text_range().is_empty());
            vec![first_recovery.clone()]
        } else {
            let group: Vec<_> = chain_children
                .iter()
                .take_while(|child| child.kind() == Error)
                .cloned()
                .collect();
            assert_eq!(group.len(), 3);
            for pair in group.windows(2) {
                assert_eq!(pair[0].text_range().end(), pair[1].text_range().start());
            }
            group
        };

        // The complete ancestry, second-arm ordinal and direct keyword select
        // the initial Condition slot before any accepted operator operand.
        // No parser record or malformed spelling participates in selection.
        assert_eq!(chain.parent(), Some(condition.clone()));
        assert_eq!(condition.parent(), Some(arms[1].clone()));
        assert_eq!(arms[1].parent(), Some(expression.clone()));
        assert_eq!(expression.parent(), Some(outer.clone()));
        assert_eq!(outer.parent(), Some(root.clone()));
        assert_eq!(arm_children[0].kind(), ElsifKw);
        let derived = match (
            condition.kind(),
            arm.kind(),
            arm_children[0].kind(),
            chain.kind(),
            first_recovery.kind(),
        ) {
            (Condition, IfArm, ElsifKw, OperatorChain, Missing | Error) => (
                CstSlot::Condition,
                [ExpectedSyntax::Expression],
                0usize,
                usize::from(recovery[0].text_range().start())
                    ..usize::from(recovery.last().unwrap().text_range().end()),
            ),
            other => panic!("unexpected initial Elsif condition slot: {other:?}"),
        };
        assert_eq!(
            derived,
            (
                CstSlot::Condition,
                [ExpectedSyntax::Expression],
                0usize,
                recovery_range
            )
        );
        let census: Vec<_> = root
            .descendants_with_tokens()
            .filter(|child| matches!(child.kind(), Missing | Error | Invalid))
            .collect();
        assert_eq!(census, recovery);
        if end == 19 {
            children(
                chain_children[3].as_node().unwrap(),
                &[
                    (Whitespace, false, 17..18, " "),
                    (Identifier, false, 18..19, "g"),
                ],
            );
        }
        let body = arm_children[5].as_node().unwrap();
        let body_children = children(body, &[(IdentifierExpression, true, end + 2..end + 3, "b")]);
        children(
            body_children[0].as_node().unwrap(),
            &[(Identifier, false, end + 2..end + 3, "b")],
        );
        assert_eq!(
            condition.text_range().end(),
            arm_children[3].text_range().start()
        );
    }
}

#[test]
fn if_selected_slots_have_exact_structural_kind_and_range_facts() {
    use CstSlot::{Body, BodyIntroducer, Condition, ElseBody};
    use StructuralKind::{ErrorGroup as Error, Missing};
    for (source, slots) in [
        ("if", vec![(Condition, StructuralKind::Missing, 2..2)]),
        ("if : y", vec![(Condition, Missing, 3..3)]),
        (
            "if :",
            vec![(Condition, Missing, 3..3), (Body, Missing, 4..4)],
        ),
        (
            "if : @",
            vec![(Condition, Missing, 3..3), (Body, Error, 5..6)],
        ),
        (
            "if x: a elsif :",
            vec![(Condition, Missing, 14..14), (Body, Missing, 15..15)],
        ),
        (
            "if x: a elsif : @",
            vec![(Condition, Missing, 14..14), (Body, Error, 16..17)],
        ),
        ("if x", vec![(BodyIntroducer, Missing, 4..4)]),
        ("if x  ", vec![(BodyIntroducer, Missing, 6..6)]),
        ("if x:", vec![(Body, Missing, 5..5)]),
        ("if x:  ", vec![(Body, Missing, 7..7)]),
        ("if x: a else", vec![(ElseBody, Missing, 12..12)]),
        ("if x: a else:", vec![(ElseBody, Missing, 13..13)]),
        ("if x: @ y", vec![(Body, Error, 6..7)]),
        ("if x: @", vec![(Body, Error, 6..7)]),
        ("if x: @  ", vec![(Body, Error, 6..7)]),
        ("if x: else a", vec![(Body, Missing, 6..6)]),
        ("if x: @ else a", vec![(Body, Error, 6..7)]),
        ("if x: elsif y: b", vec![(Body, Missing, 6..6)]),
        ("if x: @ elsif y: b", vec![(Body, Error, 6..7)]),
        ("(if x: , y)", vec![(Body, Missing, 7..7)]),
        ("(if x: @ , y)", vec![(Body, Error, 7..8)]),
        ("if x: @ @ \"α\"", vec![(Body, Error, 6..9)]),
        ("if x: ] α", vec![(Body, Error, 6..7)]),
        ("if x: [ α", vec![(Body, Error, 6..7)]),
        ("if x: @ 💥 α", vec![(Body, Error, 6..12)]),
        ("if x: @ - y", vec![(Body, Error, 6..7)]),
        ("if x: @ if y: z", vec![(Body, Error, 6..7)]),
        ("if x: a else @ y", vec![(ElseBody, Error, 13..14)]),
        ("if x: a else: @ @ y", vec![(ElseBody, Error, 14..17)]),
        ("if x: a elsif y:", vec![(Body, Missing, 16..16)]),
        ("if x: a elsif y", vec![(BodyIntroducer, Missing, 15..15)]),
        ("if x: a else if", vec![(Condition, Missing, 15..15)]),
        ("if x: a elsif y: b else: c", vec![]),
        ("if x:\n  a\nelse: b", vec![]),
    ] {
        for origin in [0, 8100] {
            let expected: Vec<StructuralFact> = slots
                .iter()
                .map(|(_, kind, range)| {
                    (
                        if *kind == Missing {
                            StructuralKind::Missing
                        } else {
                            StructuralKind::ErrorGroup
                        },
                        range.clone(),
                    )
                })
                .collect();
            for _ in 0..1 {
                let operators = OperatorTable::from_declarations([OperatorDeclaration::new(
                    "-",
                    OperatorFixities::new().with_prefix(BindingPower::scalar(70)),
                )])
                .unwrap();
                let mut recover = Recover::new_for_test(&operators);
                let mut output = GreenNodeBuilder::new();
                output.start_node(SyntaxKind::Root.into());
                let (mut exit, remainder) =
                    parse_if_into(source, origin, 0, None, &mut recover, &mut output);
                if let NormalizedExit::Complete(Err(Either::Right(end)), _) = &mut exit {
                    emit_end(&mut output, end);
                } else {
                    panic!("EOF for {source:?}");
                }
                output.finish_node();
                let green = finish_with_discarded_recoveries(output, recover);
                assert_eq!(structural_facts(&green), expected, "{source:?} at {origin}");
                assert_eq!(green.to_string(), source);
                assert_eq!(remainder, "");
            }
        }
    }
}

#[test]
fn if_completed_condition_missing_introducer_owns_ordinary_gap_only() {
    for (source, emitted, at, remaining) in [
        ("if x { body }", "if x ", 5, " body }"),
        ("if x\nnext", "if x\n", 5, ""),
        ("if α\r\nnext", "if α\r\n", 7, ""),
    ] {
        let operators = OperatorTable::from_declarations([OperatorDeclaration::new(
            "-",
            OperatorFixities::new().with_prefix(BindingPower::scalar(70)),
        )])
        .unwrap();
        let mut recover = Recover::new_for_test(&operators);
        let mut output = GreenNodeBuilder::new();
        output.start_node(SyntaxKind::Root.into());
        let (exit, suffix) = parse_if_into(source, 400, 0, None, &mut recover, &mut output);
        output.finish_node();
        let green = finish_with_discarded_recoveries(output, recover);
        assert_eq!(green.to_string(), emitted);
        assert_eq!(
            structural_facts(&green),
            [(StructuralKind::Missing, at..at)]
        );
        let NormalizedExit::Complete(Err(Either::Left(mut item)), LineEntry::InLine) = exit else {
            panic!("ordinary pending Item");
        };
        assert_eq!(emit_pending_leading_text(&mut item), "");
        assert_eq!(
            item.extent(400 + source.len() - suffix.len())
                .recovery_range(),
            400 + at..400 + source.len() - suffix.len()
        );
        assert_eq!(suffix, remaining);
    }
}

#[test]
fn if_root_and_statement_callers_publish_the_same_immediate_owner() {
    for (source, _role, kind, range) in [
        ("(if x:)", CstSlot::Body, StructuralKind::Missing, 6..6),
        ("(if x: @)", CstSlot::Body, StructuralKind::ErrorGroup, 7..8),
        (
            "if x",
            CstSlot::BodyIntroducer,
            StructuralKind::Missing,
            4..4,
        ),
        ("if x:", CstSlot::Body, StructuralKind::Missing, 5..5),
        ("if x: @ y", CstSlot::Body, StructuralKind::ErrorGroup, 6..7),
        (
            "if x: a else",
            CstSlot::ElseBody,
            StructuralKind::Missing,
            12..12,
        ),
        (
            "if x: a else: @ y",
            CstSlot::ElseBody,
            StructuralKind::ErrorGroup,
            14..15,
        ),
    ] {
        let operators = OperatorTable::empty();
        let expected = [(
            if kind == StructuralKind::Missing {
                crate::structural_diagnostic::StructuralKind::Missing
            } else {
                crate::structural_diagnostic::StructuralKind::ErrorGroup
            },
            range,
        )];
        let root = crate::cursor::parse_root(source, &operators);
        assert_eq!(root.to_string(), source);
        assert_eq!(structural_facts(&root), expected);
        let mut input = source;
        let mut recover = Recover::new_for_test(&operators);
        let mut output = GreenNodeBuilder::new();
        output.start_node(SyntaxKind::Root.into());
        let mut exit = statement_normalized(
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
        assert_eq!(green.to_string(), source);
        assert_eq!(structural_facts(&green), expected);
        assert_eq!(input, "");
    }
}

#[test]
fn if_nested_indented_body_recovery_preserves_the_dedented_item() {
    let prefix = "if outer:\n  if inner:";
    for (body, kind, relative_range) in [
        ("", StructuralKind::Missing, 21..21),
        (" @", StructuralKind::ErrorGroup, 22..23),
    ] {
        for newline in ["\n", "\r\n"] {
            let source = format!("{prefix}{body}{newline}next tail");
            let origin = 600;
            let expected = [(
                if kind == StructuralKind::Missing {
                    StructuralKind::Missing
                } else {
                    StructuralKind::ErrorGroup
                },
                relative_range.clone(),
            )];
            for _ in 0..1 {
                let operators = OperatorTable::from_declarations([OperatorDeclaration::new(
                    "-",
                    OperatorFixities::new().with_prefix(BindingPower::scalar(70)),
                )])
                .unwrap();
                let mut recover = Recover::new_for_test(&operators);
                let mut output = GreenNodeBuilder::new();
                output.start_node(SyntaxKind::Root.into());
                let (exit, suffix) =
                    parse_if_into(&source, origin, 0, None, &mut recover, &mut output);
                output.finish_node();
                let green = finish_with_discarded_recoveries(output, recover);
                assert_eq!(structural_facts(&green), expected);
                assert_eq!(green.to_string(), format!("{prefix}{body}"));
                let root = SyntaxNode::new_root(green);
                assert_eq!(
                    root.descendants()
                        .filter(|node| node.kind() == SyntaxKind::IfExpression)
                        .count(),
                    2
                );
                assert_eq!(
                    root.descendants()
                        .filter(|node| node.kind() == SyntaxKind::IndentedStatementBlock)
                        .count(),
                    1
                );
                let NormalizedExit::Complete(Err(Either::Left(mut item)), LineEntry::InLine) = exit
                else {
                    panic!("dedented next Item remains pending");
                };
                assert_eq!(token_kind(&item), Some(TokenKind::Identifier));
                assert_eq!(item.payload_view().spelling(), Some("next"));
                let successor = origin + source.len() - suffix.len();
                assert_eq!(
                    successor,
                    origin + prefix.len() + body.len() + newline.len() + 4
                );
                assert_eq!(
                    item.extent(successor).recovery_range(),
                    origin + prefix.len() + body.len()..successor
                );
                assert_eq!(emit_pending_leading_text(&mut item), newline);
                assert_eq!(suffix, " tail");
            }
        }
    }
}

#[test]
fn if_inline_boundaries_preserve_pending_payload_leading_and_successor() {
    use crate::lexical::stops::STOP_COMMA;
    for (suffix, stops, kind, leading, consumed_leading) in [
        (" , rest", STOP_COMMA, TokenKind::Comma, "", " "),
        (
            " ) rest",
            stops_for(TokenKind::RParen),
            TokenKind::RParen,
            "",
            " ",
        ),
        (" { rest", 0, TokenKind::LBrace, "", " "),
        ("\nnext rest", 0, TokenKind::Identifier, "\n", ""),
        ("\r\nnext rest", 0, TokenKind::Identifier, "\r\n", ""),
    ] {
        for head in ["if x:", "if x: a else", "if x: a else:"] {
            for error in ["", " @ @"] {
                let source = format!("{head}{error}{suffix}");
                let operators = OperatorTable::from_declarations([OperatorDeclaration::new(
                    "-",
                    OperatorFixities::new().with_prefix(BindingPower::scalar(70)),
                )])
                .unwrap();
                let mut recover = Recover::new_for_test(&operators);
                let mut output = GreenNodeBuilder::new();
                output.start_node(SyntaxKind::Root.into());
                let (exit, remainder) =
                    parse_if_into(&source, 300, stops, None, &mut recover, &mut output);
                output.finish_node();
                let green = finish_with_discarded_recoveries(output, recover);
                assert_eq!(
                    green.to_string(),
                    format!("{head}{error}{consumed_leading}")
                );
                let expected = if error.is_empty() {
                    let at = head.len() + consumed_leading.len();
                    (StructuralKind::Missing, at..at)
                } else {
                    (
                        StructuralKind::ErrorGroup,
                        head.len() + 1..head.len() + error.len(),
                    )
                };
                assert_eq!(structural_facts(&green), [expected], "{source:?}");
                let NormalizedExit::Complete(Err(Either::Left(mut item)), line) = exit else {
                    panic!("pending {source:?}");
                };
                assert_eq!(line, LineEntry::InLine);
                assert_eq!(token_kind(&item), Some(kind));
                assert_eq!(
                    item.extent(300 + source.len() - remainder.len())
                        .recovery_range(),
                    300 + green.to_string().len()..300 + source.len() - remainder.len()
                );
                assert_eq!(emit_pending_leading_text(&mut item), leading);
                assert_eq!(remainder, " rest");
            }
        }
    }
}

#[test]
fn if_quoted_fences_remain_wholly_pending_before_and_after_errors() {
    use crate::lexical::yumark::{FenceOpener, FencePrefixPolicy};
    let fence = FenceBoundary {
        opener: FenceOpener {
            line: 0,
            marker: 0..3,
            marker_width: 3,
        },
        prefix_policy: FencePrefixPolicy::ActivePrefixQuote { depth: 2, base: 0 },
        close_column: 0,
    };
    for (head, role) in [
        ("if x", CstSlot::BodyIntroducer),
        ("if x:", CstSlot::Body),
        ("if x: a else", CstSlot::ElseBody),
        ("if x: a else:", CstSlot::ElseBody),
    ] {
        for error in ["", " @ 💥"] {
            if role == CstSlot::BodyIntroducer && !error.is_empty() {
                continue;
            }
            for newline in ["\n", "\r\n"] {
                let accepted = format!("{head}{error}");
                let source = format!("{accepted}{newline}> > ```{newline}outer");
                let operators = OperatorTable::from_declarations([OperatorDeclaration::new(
                    "-",
                    OperatorFixities::new().with_prefix(BindingPower::scalar(70)),
                )])
                .unwrap();
                let mut recover = Recover::new_for_test(&operators);
                let mut output = GreenNodeBuilder::new();
                output.start_node(SyntaxKind::Root.into());
                let (exit, remainder) =
                    parse_if_into(&source, 700, 0, Some(&fence), &mut recover, &mut output);
                output.finish_node();
                let green = finish_with_discarded_recoveries(output, recover);
                assert_eq!(green.to_string(), accepted);
                let coordinate = 700 + accepted.len() + newline.len();
                let expected = if error.is_empty() {
                    (StructuralKind::Missing, accepted.len()..accepted.len())
                } else {
                    (StructuralKind::ErrorGroup, head.len() + 1..accepted.len())
                };
                assert_eq!(structural_facts(&green), [expected], "{source:?}");
                let NormalizedExit::Complete(Err(Either::Left(item)), LineEntry::PhysicalStart) =
                    exit
                else {
                    panic!("protected fence");
                };
                let (leading, boundary) = emit_terminal_leading_text(item);
                assert_eq!(leading, newline);
                assert_eq!(boundary.coordinate(), coordinate);
                assert_eq!(remainder, format!("> > ```{newline}outer"));
            }
        }
    }
}

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
            .descendants_with_tokens()
            .any(|node| matches!(node.kind(), SyntaxKind::Error | SyntaxKind::Invalid))
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
            crate::tests::recovery_output::recovery_groups(&root)
                .into_iter()
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
