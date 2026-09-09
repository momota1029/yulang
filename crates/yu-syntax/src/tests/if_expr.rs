use crate::tests::support::*;
use crate::{
    ambient_claim::AmbientClaimView,
    handoff::MlMode,
    recovery_record::{
        DiagnosticId, ExpectationSources, ExpectedSyntax, GrammarRole, IfExpressionRole,
        PunctuationEvidence, RecoveryKind, RecoverySiteKey, SyntaxExpectation, UnexpectedCategory,
        UnexpectedSyntax,
    },
    statement::StatementLineHandoff,
};
use std::{ops::Range, sync::Arc};

fn if_record(
    id: u32,
    role: IfExpressionRole,
    kind: RecoveryKind,
    range: Range<usize>,
) -> CommittedRecoveryRecord {
    let expected = match role {
        IfExpressionRole::BodyIntroducer => ExpectedSyntax::Punctuation(PunctuationEvidence::Colon),
        _ => ExpectedSyntax::Expression,
    };
    let role = GrammarRole::IfExpression(role);
    CommittedRecoveryRecord {
        id: DiagnosticId(id),
        site: RecoverySiteKey {
            role,
            range: range.clone(),
        },
        kind,
        unexpected: if kind == RecoveryKind::Missing {
            Arc::from([])
        } else {
            Arc::from([UnexpectedSyntax::Token {
                range: range.clone(),
                category: UnexpectedCategory::OtherCharacter,
            }])
        },
        expectations: Arc::from([SyntaxExpectation {
            role,
            expected,
            range,
            sources: ExpectationSources::COMMITTED_RECOVERY_RULE,
        }]),
        primary_expectation: 0,
    }
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
fn if_selected_slots_have_exact_fresh_shifted_and_frozen_records() {
    use IfExpressionRole::{Body, BodyIntroducer, Condition, ElseBody};
    use RecoveryKind::{Error, Missing};
    for (source, slots) in [
        ("if", vec![(Condition, Missing, 2..2)]),
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
            let expected: Vec<_> = slots
                .iter()
                .enumerate()
                .map(|(id, (role, kind, range))| {
                    if_record(
                        id as u32,
                        *role,
                        *kind,
                        origin + range.start..origin + range.end,
                    )
                })
                .collect();
            let mut fresh = None;
            for frozen in [None, Some(expected.as_slice())] {
                let operators = OperatorTable::from_declarations([OperatorDeclaration::new(
                    "-",
                    OperatorFixities::new().with_prefix(BindingPower::scalar(70)),
                )])
                .unwrap();
                let mut recover = Recover::new_for_test(&operators);
                let mut output = frozen
                    .map(|records| {
                        recover = Recover::reconcile_for_test(recover.operators(), records);
                        GreenNodeBuilder::new()
                    })
                    .unwrap_or_else(GreenNodeBuilder::new);
                output.start_node(SyntaxKind::Root.into());
                let (mut exit, remainder) =
                    parse_if_into(source, origin, 0, None, &mut recover, &mut output);
                if let NormalizedExit::Complete(Err(Either::Right(end)), _) = &mut exit {
                    emit_end(&mut output, end);
                } else {
                    panic!("EOF for {source:?}");
                }
                output.finish_node();
                let (green, records) = (output.finish(), recover.finish_recoveries_for_test());
                assert_eq!(records, expected, "{source:?} at {origin}");
                assert_eq!(green.to_string(), source);
                assert_eq!(remainder, "");
                if let Some(fresh) = &fresh {
                    assert_eq!(&green, fresh);
                } else {
                    fresh = Some(green);
                }
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
        let (green, records) = (output.finish(), recover.finish_recoveries_for_test());
        assert_eq!(green.to_string(), emitted);
        assert_eq!(
            records,
            [if_record(
                0,
                IfExpressionRole::BodyIntroducer,
                RecoveryKind::Missing,
                400 + at..400 + at
            )]
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
    for (source, role, kind, range) in [
        (
            "(if x:)",
            IfExpressionRole::Body,
            RecoveryKind::Missing,
            6..6,
        ),
        (
            "(if x: @)",
            IfExpressionRole::Body,
            RecoveryKind::Error,
            7..8,
        ),
        (
            "if x",
            IfExpressionRole::BodyIntroducer,
            RecoveryKind::Missing,
            4..4,
        ),
        ("if x:", IfExpressionRole::Body, RecoveryKind::Missing, 5..5),
        (
            "if x: @ y",
            IfExpressionRole::Body,
            RecoveryKind::Error,
            6..7,
        ),
        (
            "if x: a else",
            IfExpressionRole::ElseBody,
            RecoveryKind::Missing,
            12..12,
        ),
        (
            "if x: a else: @ y",
            IfExpressionRole::ElseBody,
            RecoveryKind::Error,
            14..15,
        ),
    ] {
        let operators = OperatorTable::empty();
        let expected = [if_record(0, role, kind, range)];
        let root = crate::source_file::parse_root_candidate(source, &operators, &[]);
        assert_eq!(root.green.to_string(), source);
        assert_eq!(root.committed_recoveries.as_slice(), expected);
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
        let (green, records) = (output.finish(), recover.finish_recoveries_for_test());
        assert_eq!(green.to_string(), source);
        assert_eq!(records, expected);
        assert_eq!(input, "");
    }
}

#[test]
fn if_nested_indented_body_recovery_preserves_the_dedented_item() {
    let prefix = "if outer:\n  if inner:";
    for (body, kind, relative_range) in [
        ("", RecoveryKind::Missing, 21..21),
        (" @", RecoveryKind::Error, 22..23),
    ] {
        for newline in ["\n", "\r\n"] {
            let source = format!("{prefix}{body}{newline}next tail");
            let origin = 600;
            let expected = [if_record(
                0,
                IfExpressionRole::Body,
                kind,
                origin + relative_range.start..origin + relative_range.end,
            )];
            for frozen in [None, Some(expected.as_slice())] {
                let operators = OperatorTable::from_declarations([OperatorDeclaration::new(
                    "-",
                    OperatorFixities::new().with_prefix(BindingPower::scalar(70)),
                )])
                .unwrap();
                let mut recover = Recover::new_for_test(&operators);
                let mut output = frozen
                    .map(|records| {
                        recover = Recover::reconcile_for_test(recover.operators(), records);
                        GreenNodeBuilder::new()
                    })
                    .unwrap_or_else(GreenNodeBuilder::new);
                output.start_node(SyntaxKind::Root.into());
                let (exit, suffix) =
                    parse_if_into(&source, origin, 0, None, &mut recover, &mut output);
                output.finish_node();
                let (green, records) = (output.finish(), recover.finish_recoveries_for_test());
                assert_eq!(records, expected);
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
fn if_slots_reuse_seeded_and_frozen_ids_and_allocate_above_them() {
    for (source, role, kind, range) in [
        (
            "if x",
            IfExpressionRole::BodyIntroducer,
            RecoveryKind::Missing,
            4..4,
        ),
        ("if x:", IfExpressionRole::Body, RecoveryKind::Missing, 5..5),
        (
            "if x: @ y",
            IfExpressionRole::Body,
            RecoveryKind::Error,
            6..7,
        ),
        (
            "if x: a else",
            IfExpressionRole::ElseBody,
            RecoveryKind::Missing,
            12..12,
        ),
        (
            "if x: a else: @ y",
            IfExpressionRole::ElseBody,
            RecoveryKind::Error,
            14..15,
        ),
    ] {
        let seed = if_record(7, IfExpressionRole::Condition, RecoveryKind::Missing, 0..0);
        let reused = if_record(19, role, kind, 100 + range.start..100 + range.end);
        let frozen = [seed.clone(), reused.clone()];
        let operators = OperatorTable::from_declarations([OperatorDeclaration::new(
            "-",
            OperatorFixities::new().with_prefix(BindingPower::scalar(70)),
        )])
        .unwrap();
        let mut recover = Recover::new_for_test(&operators);
        let mut output = {
            recover = Recover::reconcile_for_test(recover.operators(), &frozen);
            GreenNodeBuilder::new()
        };
        output.start_node(SyntaxKind::Root.into());
        output.start_node(SyntaxKind::Missing.into());
        output.finish_node();
        recover.commit_recovery_for_test(crate::cursor::recovery::RecoveryDraft::new(
            seed.site.clone(),
            seed.kind,
            seed.unexpected.clone(),
            seed.expectations.clone(),
            0,
        ));
        for origin in [100, 200] {
            let _ = parse_if_into(source, origin, 0, None, &mut recover, &mut output);
        }
        output.finish_node();
        let (_, records) = (output.finish(), recover.finish_recoveries_for_test());
        assert_eq!(
            records,
            [
                seed,
                reused,
                if_record(20, role, kind, 200 + range.start..200 + range.end)
            ]
        );
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
                let (green, records) = (output.finish(), recover.finish_recoveries_for_test());
                assert_eq!(
                    green.to_string(),
                    format!("{head}{error}{consumed_leading}")
                );
                let role = if head == "if x:" {
                    IfExpressionRole::Body
                } else {
                    IfExpressionRole::ElseBody
                };
                let (recovery_kind, range) = if error.is_empty() {
                    let at = 300 + head.len() + consumed_leading.len();
                    (RecoveryKind::Missing, at..at)
                } else {
                    (
                        RecoveryKind::Error,
                        301 + head.len()..300 + head.len() + error.len(),
                    )
                };
                assert_eq!(
                    records,
                    [if_record(0, role, recovery_kind, range)],
                    "{source:?}"
                );
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
        ("if x", IfExpressionRole::BodyIntroducer),
        ("if x:", IfExpressionRole::Body),
        ("if x: a else", IfExpressionRole::ElseBody),
        ("if x: a else:", IfExpressionRole::ElseBody),
    ] {
        for error in ["", " @ 💥"] {
            if role == IfExpressionRole::BodyIntroducer && !error.is_empty() {
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
                let (green, records) = (output.finish(), recover.finish_recoveries_for_test());
                assert_eq!(green.to_string(), accepted);
                let coordinate = 700 + accepted.len() + newline.len();
                let (kind, range) = if error.is_empty() {
                    (RecoveryKind::Missing, coordinate..coordinate)
                } else {
                    (RecoveryKind::Error, 701 + head.len()..700 + accepted.len())
                };
                assert_eq!(records, [if_record(0, role, kind, range)], "{source:?}");
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
