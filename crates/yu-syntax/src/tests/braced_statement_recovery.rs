use crate::tests::support::*;
use crate::{ambient_claim::AmbientClaimView, recovery_record::*};
use std::{ops::Range, sync::Arc};

fn parse<'s>(
    source: &'s str,
    origin: usize,
    fence: Option<&FenceBoundary>,
    frozen: Option<&[CommittedRecoveryRecord]>,
) -> (
    GreenNode,
    Vec<CommittedRecoveryRecord>,
    NormalizedExit,
    &'s str,
) {
    let operators = OperatorTable::empty();
    let mut recover = Recover::new_for_test(&operators);
    let mut input = source;
    let mut output = frozen
        .map(|records| {
            recover = Recover::reconcile_for_test(recover.operators(), records);
            GreenNodeBuilder::new()
        })
        .unwrap_or_else(GreenNodeBuilder::new);
    output.start_node(SyntaxKind::Root.into());
    let exit = statement_normalized(
        crate::cursor::SyntaxIn::new(&mut input, &mut recover, &mut output),
        0,
        0,
        origin,
        LineEntry::InLine,
        fence,
        Some(AmbientClaimView::root_statement(0)).into(),
        Some(crate::sequence::SequenceOwner::RootStatement),
    );
    output.finish_node();
    let (green, records) = (output.finish(), recover.finish_recoveries_for_test());
    (green, records, exit, input)
}

fn record(
    id: usize,
    role: GrammarRole,
    range: Range<usize>,
    error: bool,
) -> CommittedRecoveryRecord {
    let expected = match role {
        GrammarRole::BracedStatementBlock(BracedStatementBlockRole::Statement) => {
            ExpectedSyntax::Statement
        }
        GrammarRole::BracedStatementBlock(BracedStatementBlockRole::Separator) => {
            ExpectedSyntax::StatementSeparator
        }
        GrammarRole::ClosingDelimiter { delimiter, .. } => {
            ExpectedSyntax::Punctuation(PunctuationEvidence::Close(delimiter))
        }
        _ => unreachable!(),
    };
    CommittedRecoveryRecord {
        id: DiagnosticId(id as u32),
        site: RecoverySiteKey {
            role,
            range: range.clone(),
        },
        kind: if error {
            RecoveryKind::Error
        } else {
            RecoveryKind::Missing
        },
        unexpected: if error {
            Arc::from([UnexpectedSyntax::Token {
                range: range.clone(),
                category: UnexpectedCategory::OtherCharacter,
            }])
        } else {
            Arc::from([])
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

#[test]
fn braced_slots_have_exact_shifted_and_frozen_records() {
    let statement = GrammarRole::BracedStatementBlock(BracedStatementBlockRole::Statement);
    let separator = GrammarRole::BracedStatementBlock(BracedStatementBlockRole::Separator);
    let close = GrammarRole::ClosingDelimiter {
        owner: ConstructRole::BracedStatementBlockExpression,
        delimiter: Delimiter::Brace,
    };
    for (source, slots) in [
        (
            "{,;}",
            vec![(statement, 1..1, false), (statement, 2..2, false)],
        ),
        ("{ @ @ α}", vec![(statement, 2..5, true)]),
        ("{@,}", vec![(statement, 1..2, true)]),
        (
            "{@\n,}",
            vec![(statement, 1..2, true), (statement, 3..3, false)],
        ),
        (
            "{@\r\n;}",
            vec![(statement, 1..2, true), (statement, 4..4, false)],
        ),
        ("{x\n;}", vec![(statement, 3..3, false)]),
        ("{x\r\n,}", vec![(statement, 4..4, false)]),
        ("{@}", vec![(statement, 1..2, true)]),
        ("{@  ", vec![(statement, 1..2, true), (close, 4..4, false)]),
        ("{  ", vec![(close, 3..3, false)]),
        ("{use a use b}", vec![(separator, 6..6, false)]),
    ] {
        for origin in [0, 137] {
            let expected: Vec<_> = slots
                .iter()
                .enumerate()
                .map(|(id, (role, range, error))| {
                    record(id, *role, origin + range.start..origin + range.end, *error)
                })
                .collect();
            let (green, records, _, _) = parse(source, origin, None, None);
            assert_eq!(green.to_string(), source);
            assert_eq!(records, expected, "{source:?}");
            let (again, frozen, _, _) = parse(source, origin, None, Some(&records));
            assert_eq!(again, green);
            assert_eq!(frozen, records);
        }
    }
}

#[test]
fn braced_missing_slots_collide_at_the_same_direct_rowan_occurrence_path() {
    let statement = GrammarRole::BracedStatementBlock(BracedStatementBlockRole::Statement);
    let separator = GrammarRole::BracedStatementBlock(BracedStatementBlockRole::Separator);
    let close = GrammarRole::ClosingDelimiter {
        owner: ConstructRole::BracedStatementBlockExpression,
        delimiter: Delimiter::Brace,
    };
    let cases = [
        // The comma and semicolon remain in their explicit separator phase.
        (
            "{,;}",
            statement,
            1..1,
            vec![
                record(0, statement, 1..1, false),
                record(1, statement, 2..2, false),
            ],
        ),
        // The second statement is admitted after the missing separator.
        (
            "{use a use b}",
            separator,
            6..6,
            vec![record(0, separator, 6..6, false)],
        ),
        // EOF reaches the local close phase after its horizontal leading.
        ("{  ", close, 3..3, vec![record(0, close, 3..3, false)]),
    ];

    let mut paths = Vec::new();
    for (source, role, range, expected) in cases {
        let (green, records, exit, suffix) = parse(source, 0, None, None);
        assert_eq!(green.to_string(), source, "{source:?}");
        assert_eq!(records, expected, "{source:?}");
        assert!(matches!(exit, NormalizedExit::Complete(_, _)), "{source:?}");
        assert_eq!(suffix, "", "{source:?}");

        let root = SyntaxNode::new_root(green.clone());
        let block = root
            .descendants()
            .find(|node| node.kind() == SyntaxKind::BracedStatementBlockExpression)
            .unwrap_or_else(|| panic!("braced block for {source:?}"));
        // Immediate ancestry is shared, but the complete ordered direct
        // children retain the required-item, successor and terminal phases.
        // Select the occurrence by that order, independently of the ledger.
        let children = block.children_with_tokens().collect::<Vec<_>>();
        let (kinds, missing_index) = match source {
            "{,;}" => (
                vec![
                    SyntaxKind::LBrace,
                    SyntaxKind::Missing,
                    SyntaxKind::BlockStatementSeparator,
                    SyntaxKind::Missing,
                    SyntaxKind::BlockStatementSeparator,
                    SyntaxKind::RBrace,
                ],
                1,
            ),
            "{use a use b}" => (
                vec![
                    SyntaxKind::LBrace,
                    SyntaxKind::Statement,
                    SyntaxKind::Missing,
                    SyntaxKind::Statement,
                    SyntaxKind::RBrace,
                ],
                2,
            ),
            "{  " => (
                vec![
                    SyntaxKind::LBrace,
                    SyntaxKind::Whitespace,
                    SyntaxKind::Missing,
                ],
                2,
            ),
            _ => unreachable!(),
        };
        assert_eq!(
            children
                .iter()
                .map(|child| child.kind())
                .collect::<Vec<_>>(),
            kinds,
            "{source:?}",
        );
        for child in &children {
            assert_eq!(child.parent(), Some(block.clone()), "{source:?}");
            assert_eq!(
                child.as_node().is_some(),
                matches!(
                    child.kind(),
                    SyntaxKind::Missing
                        | SyntaxKind::Statement
                        | SyntaxKind::BlockStatementSeparator
                ),
                "{source:?}",
            );
        }
        assert!(
            !block
                .descendants()
                .any(|node| node.kind() == SyntaxKind::Invalid)
        );
        let missing = children[missing_index].as_node().unwrap();
        assert_eq!(missing.kind(), SyntaxKind::Missing);
        assert_eq!(
            missing.text_range(),
            rowan::TextRange::empty(range.start.into())
        );
        assert_eq!(missing.text().to_string(), "", "{role:?}: {source:?}");
        assert!(missing.children_with_tokens().next().is_none());
        if source == "{,;}" {
            for (index, kind, text) in
                [(2, SyntaxKind::Comma, ","), (4, SyntaxKind::Semicolon, ";")]
            {
                let separator = children[index].as_node().unwrap();
                let tokens = separator.children_with_tokens().collect::<Vec<_>>();
                assert_eq!(tokens.len(), 1);
                let token = tokens[0].as_token().unwrap();
                assert_eq!(token.kind(), kind);
                assert_eq!(token.text(), text);
            }
        }
        if source == "{  " {
            let leading = children[1].as_token().unwrap();
            assert_eq!(leading.text(), "  ");
            assert_eq!(
                leading.text_range(),
                rowan::TextRange::new(1.into(), 3.into())
            );
            assert_eq!(missing_index + 1, children.len());
        } else {
            let close = children.last().unwrap().as_token().unwrap();
            assert_eq!(close.kind(), SyntaxKind::RBrace);
            assert_eq!(close.text(), "}");
            assert_eq!(usize::from(close.text_range().end()), source.len());
        }
        assert_eq!(missing.parent(), Some(block.clone()), "{source:?}");
        paths.push(
            missing
                .ancestors()
                .take(2)
                .map(|node| node.kind())
                .collect::<Vec<_>>(),
        );

        if role == separator {
            assert_eq!(
                block
                    .children()
                    .filter(|node| node.kind() == SyntaxKind::Statement)
                    .count(),
                2,
                "the second Statement follows its missing separator: {source:?}",
            );
        }

        let (again, frozen, frozen_exit, frozen_suffix) = parse(source, 0, None, Some(&records));
        assert_eq!(again, green, "{source:?}");
        assert_eq!(frozen, records, "{source:?}");
        assert!(
            matches!(frozen_exit, NormalizedExit::Complete(_, _)),
            "{source:?}"
        );
        assert_eq!(frozen_suffix, suffix, "{source:?}");
    }

    assert_eq!(
        paths,
        vec![
            vec![
                SyntaxKind::Missing,
                SyntaxKind::BracedStatementBlockExpression
            ],
            vec![
                SyntaxKind::Missing,
                SyntaxKind::BracedStatementBlockExpression
            ],
            vec![
                SyntaxKind::Missing,
                SyntaxKind::BracedStatementBlockExpression
            ],
        ],
        "the roles have no CST-visible wrapper between the block and Missing",
    );
}

#[test]
fn protected_nonlocal_closes_keep_horizontal_and_crlf_leading() {
    for prefix in ["{", "{@", "{x;", "{x", "{for x in xs {}"] {
        for leading in ["  ", "\r\n  "] {
            for close in [')', ']'] {
                let source = format!("{prefix}{leading}{close}tail");
                let (green, records, exit, suffix) = parse(&source, 100, None, None);
                assert_eq!(green.to_string(), prefix);
                assert_eq!(suffix, "tail");
                let NormalizedExit::Complete(Err(Either::Left(item)), _) = exit else {
                    panic!("protected close")
                };
                assert_eq!(
                    item.extent(100 + source.len() - suffix.len())
                        .recovery_range(),
                    100 + prefix.len()..100 + prefix.len() + leading.len() + 1
                );
                assert_eq!(
                    records.last().unwrap().site.range,
                    100 + prefix.len()..100 + prefix.len()
                );
            }
        }
    }
}

#[test]
fn accepted_braced_sequence_controls_stay_record_free() {
    for source in [
        "{}", "{ }", "{x;}", "{x,}", "{x;  ", "{f x}", "{f: x,y}", "{x\n y}",
    ] {
        let (green, records, _, _) = parse(source, 0, None, None);
        assert_eq!(green.to_string(), source);
        if source.ends_with('}') {
            assert!(records.is_empty(), "{source:?}: {records:?}");
        } else {
            assert_eq!(records.len(), 1);
        }
    }
}

#[test]
fn declaration_body_callers_publish_the_braced_child_role() {
    for prefix in ["mod M ", "role R ", "impl T ", "act A ", "for x in xs "] {
        let source = format!("{prefix}{{ @ }}");
        let (green, records, _, _) = parse(&source, 0, None, None);
        assert_eq!(green.to_string(), source);
        assert_eq!(
            records,
            [record(
                0,
                GrammarRole::BracedStatementBlock(BracedStatementBlockRole::Statement),
                prefix.len() + 2..prefix.len() + 3,
                true
            )],
            "{source:?}"
        );
        let (again, frozen, _, _) = parse(&source, 0, None, Some(&records));
        assert_eq!(again, green);
        assert_eq!(frozen, records);
    }
}

#[test]
fn declaration_body_callers_return_protected_closes_with_leading() {
    let role = GrammarRole::ClosingDelimiter {
        owner: ConstructRole::BracedStatementBlockExpression,
        delimiter: Delimiter::Brace,
    };
    for prefix in ["mod M ", "role R ", "impl T ", "act A ", "for x in xs "] {
        for leading in ["  ", "\r\n  "] {
            for close in [')', ']'] {
                let owned = format!("{prefix}{{x");
                let source = format!("{owned}{leading}{close}tail");
                let (green, records, exit, suffix) = parse(&source, 100, None, None);
                assert_eq!(green.to_string(), owned, "{source:?}");
                let at = 100 + owned.len();
                assert_eq!(records, [record(0, role, at..at, false)], "{source:?}");
                let NormalizedExit::Complete(Err(Either::Left(item)), _) = exit else {
                    panic!("protected close: {source:?}")
                };
                assert_eq!(suffix, "tail");
                assert_eq!(
                    item.extent(100 + source.len() - suffix.len())
                        .recovery_range(),
                    at..at + leading.len() + 1
                );
                let (again, frozen, _, remainder) = parse(&source, 100, None, Some(&records));
                assert_eq!(again, green);
                assert_eq!(frozen, records);
                assert_eq!(remainder, suffix);
            }
        }
    }
}

#[test]
fn error_run_stops_at_quoted_fence_and_qualifying_newline() {
    use crate::lexical::yumark::{FenceOpener, FencePrefixPolicy};
    let fence = FenceBoundary {
        opener: FenceOpener {
            line: 0,
            marker: 0..3,
            marker_width: 3,
        },
        prefix_policy: FencePrefixPolicy::ActivePrefixQuote { depth: 1, base: 0 },
        close_column: 0,
    };
    let source = "{ 💥\r\n> ```\nouter";
    let (green, records, exit, suffix) = parse(source, 100, Some(&fence), None);
    assert_eq!(green.to_string(), "{ 💥");
    assert_eq!(
        records,
        [
            record(
                0,
                GrammarRole::BracedStatementBlock(BracedStatementBlockRole::Statement),
                102..106,
                true
            ),
            record(
                1,
                GrammarRole::ClosingDelimiter {
                    owner: ConstructRole::BracedStatementBlockExpression,
                    delimiter: Delimiter::Brace
                },
                108..108,
                false
            )
        ]
    );
    assert!(matches!(
        exit,
        NormalizedExit::Complete(Err(Either::Left(_)), _)
    ));
    assert_eq!(suffix, "> ```\nouter");
    let (again, frozen, _, _) = parse(source, 100, Some(&fence), Some(&records));
    assert_eq!(again, green);
    assert_eq!(frozen, records);
    let (green, records, _, _) = parse("{ @\n@ x}", 0, None, None);
    assert_eq!(green.to_string(), "{ @\n@ x}");
    assert_eq!(
        records,
        [
            record(
                0,
                GrammarRole::BracedStatementBlock(BracedStatementBlockRole::Statement),
                2..3,
                true
            ),
            record(
                1,
                GrammarRole::BracedStatementBlock(BracedStatementBlockRole::Statement),
                4..5,
                true
            )
        ]
    );
}

#[test]
fn optional_statement_rejection_is_effect_free() {
    let (green, records, exit, suffix) = parse("@ rest", 0, None, None);
    assert_eq!(green.to_string(), "");
    assert!(records.is_empty());
    assert!(matches!(
        exit,
        NormalizedExit::Complete(Err(Either::Left(_)), _)
    ));
    assert_eq!(suffix, " rest");
}

#[test]
fn nested_for_braced_body_success_resumes_the_enclosing_sequence() {
    let separator = GrammarRole::BracedStatementBlock(BracedStatementBlockRole::Separator);
    for (source, expected_records) in [
        ("{for x in xs {}}", vec![]),
        (
            "{for x in xs {} use a}",
            vec![record(0, separator, 15..15, false)],
        ),
        ("{for x in xs {}; use a}", vec![]),
        ("{for x in xs {}, use a}", vec![]),
        ("{for x in xs {}\nuse a}", vec![]),
        ("{for x in xs {}\r\nuse a}", vec![]),
    ] {
        let (green, records, exit, suffix) = parse(source, 0, None, None);
        assert_eq!(green.to_string(), source, "{source:?}");
        assert_eq!(records, expected_records, "{source:?}");
        assert!(matches!(
            exit,
            NormalizedExit::Complete(Err(Either::Right(_)), _)
        ));
        assert_eq!(suffix, "", "{source:?}");

        if matches!(source, "{for x in xs {}}" | "{for x in xs {} use a}") {
            let root = SyntaxNode::new_root(green.clone());
            let block = root
                .descendants()
                .find(|node| node.kind() == SyntaxKind::BracedStatementBlockExpression)
                .unwrap();
            let children = block.children_with_tokens().collect::<Vec<_>>();
            let expected_kinds = if source == "{for x in xs {}}" {
                vec![
                    SyntaxKind::LBrace,
                    SyntaxKind::Statement,
                    SyntaxKind::RBrace,
                ]
            } else {
                vec![
                    SyntaxKind::LBrace,
                    SyntaxKind::Statement,
                    SyntaxKind::Missing,
                    SyntaxKind::Statement,
                    SyntaxKind::RBrace,
                ]
            };
            assert_eq!(
                children
                    .iter()
                    .map(|child| child.kind())
                    .collect::<Vec<_>>(),
                expected_kinds,
                "{source:?}",
            );
            for child in &children {
                assert_eq!(child.parent(), Some(block.clone()));
                assert_eq!(
                    child.as_node().is_some(),
                    matches!(child.kind(), SyntaxKind::Statement | SyntaxKind::Missing),
                );
            }
            let close = children.last().unwrap().as_token().unwrap();
            assert_eq!(close.kind(), SyntaxKind::RBrace);
            assert_eq!(close.text(), "}");
            assert_eq!(
                close.text_range(),
                rowan::TextRange::new(
                    (source.len() as u32 - 1).into(),
                    (source.len() as u32).into()
                ),
            );
            assert!(
                !block
                    .descendants()
                    .any(|node| node.kind() == SyntaxKind::Invalid)
            );
            let nested = children[1]
                .as_node()
                .unwrap()
                .descendants()
                .find(|node| node.kind() == SyntaxKind::BracedStatementBlockExpression)
                .unwrap();
            assert_eq!(nested.text().to_string(), "{}");
            assert_eq!(
                nested
                    .children_with_tokens()
                    .map(|child| child.kind())
                    .collect::<Vec<_>>(),
                vec![SyntaxKind::LBrace, SyntaxKind::RBrace],
            );
            if source == "{for x in xs {} use a}" {
                let missing = children[2].as_node().unwrap();
                assert_eq!(missing.text_range(), rowan::TextRange::empty(15.into()));
                assert!(missing.children_with_tokens().next().is_none());
                assert_eq!(
                    missing
                        .ancestors()
                        .take(2)
                        .map(|node| node.kind())
                        .collect::<Vec<_>>(),
                    vec![
                        SyntaxKind::Missing,
                        SyntaxKind::BracedStatementBlockExpression
                    ],
                );
            }
        }

        let (again, frozen, frozen_exit, frozen_suffix) = parse(source, 0, None, Some(&records));
        assert_eq!(again, green, "{source:?}");
        assert_eq!(frozen, records, "{source:?}");
        assert!(matches!(
            frozen_exit,
            NormalizedExit::Complete(Err(Either::Right(_)), _)
        ));
        assert_eq!(frozen_suffix, suffix, "{source:?}");
    }
}
