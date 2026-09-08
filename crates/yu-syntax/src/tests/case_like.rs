use crate::tests::support::*;
use crate::{
    ambient_claim::AmbientClaimView,
    handoff::MlMode,
    recovery_record::{
        CaseLikeRole, DiagnosticId, ExpectationSources, ExpectedSyntax, GrammarRole,
        PunctuationEvidence, RecoveryKind, RecoverySiteKey, SyntaxExpectation, UnexpectedCategory,
        UnexpectedSyntax,
    },
    statement::StatementLineHandoff,
};
use std::{ops::Range, sync::Arc};

fn arm_record(
    id: u32,
    role: CaseLikeRole,
    range: Range<usize>,
    combined: bool,
    tokens: &[Range<usize>],
) -> CommittedRecoveryRecord {
    let mut record = structural_record(
        id,
        role,
        if tokens.is_empty() {
            RecoveryKind::Missing
        } else {
            RecoveryKind::Error
        },
        range.clone(),
    );
    let mut expectations = vec![SyntaxExpectation {
        role: GrammarRole::CaseLike(role),
        expected: if role == CaseLikeRole::Arrow {
            ExpectedSyntax::Punctuation(PunctuationEvidence::Arrow)
        } else {
            ExpectedSyntax::Expression
        },
        range: range.clone(),
        sources: ExpectationSources::COMMITTED_RECOVERY_RULE,
    }];
    if combined {
        expectations.push(SyntaxExpectation {
            role: GrammarRole::CaseLike(CaseLikeRole::Body),
            expected: ExpectedSyntax::Expression,
            range,
            sources: ExpectationSources::COMMITTED_RECOVERY_RULE,
        });
    }
    record.expectations = expectations.into();
    record.unexpected = tokens
        .iter()
        .map(|range| UnexpectedSyntax::Token {
            range: range.clone(),
            category: UnexpectedCategory::OtherCharacter,
        })
        .collect();
    record
}

fn without_arm_records(records: &[CommittedRecoveryRecord]) -> Vec<CommittedRecoveryRecord> {
    records
        .iter()
        .filter(|record| {
            !matches!(
                record.site.role,
                GrammarRole::CaseLike(CaseLikeRole::Arrow | CaseLikeRole::Body)
            )
        })
        .cloned()
        .collect()
}

fn structural_record(
    id: u32,
    role: CaseLikeRole,
    kind: RecoveryKind,
    range: Range<usize>,
) -> CommittedRecoveryRecord {
    let expected = if role == CaseLikeRole::Block {
        ExpectedSyntax::Punctuation(PunctuationEvidence::Colon)
    } else {
        ExpectedSyntax::Pattern
    };
    let role = GrammarRole::CaseLike(role);
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

fn parse_case_into<'s>(
    source: &'s str,
    origin: usize,
    fence: Option<&FenceBoundary>,
    output: &mut GreenNodeBuilder,
) -> (NormalizedExit, &'s str) {
    let operators = OperatorTable::empty();
    let mut recover = Recover::new(&operators);
    let mut input = source;
    let exit = expr_normalized(
        In::new(&mut input, &mut recover, output),
        None,
        0,
        0,
        MlMode::All,
        StatementLineHandoff::OrdinaryLayout,
        origin,
        LineEntry::InLine,
        fence,
        Some(AmbientClaimView::root_statement(0)).into(),
        None,
    )
    .expect("CaseLike expression");
    (exit, input)
}

#[test]
fn case_structural_slots_have_exact_fresh_shifted_frozen_and_seeded_records() {
    use CaseLikeRole::{Arm, Block, Handler, Pattern};
    use RecoveryKind::{Error, Missing};
    for (source, role, kind, range) in [
        ("case x", Block, Missing, 6..6),
        ("catch action", Block, Missing, 12..12),
        ("case x  ", Block, Missing, 8..8),
        ("catch action  ", Block, Missing, 14..14),
        ("case x: -> a", Pattern, Missing, 8..8),
        ("case x:", Pattern, Missing, 7..7),
        ("catch x: err,", Handler, Missing, 13..13),
        ("catch action: err, -> recover", Handler, Missing, 18..18),
        ("case x:\nnext", Arm, Missing, 7..7),
        ("catch x:\nnext", Arm, Missing, 8..8),
        ("case x: @ n -> a", Pattern, Error, 8..9),
        ("case x: @", Pattern, Error, 8..9),
        ("catch x: @ err -> a", Pattern, Error, 9..10),
        ("catch x: err, @ handler -> a", Handler, Error, 13..15),
        ("case α: @ 💥 n -> a", Pattern, Error, 9..15),
        ("(case x)", Block, Missing, 7..7),
        ("(case x: -> a)", Pattern, Missing, 9..9),
        ("(catch action: err, -> recover)", Handler, Missing, 19..19),
    ] {
        for origin in [0, 8100] {
            let expected = [structural_record(
                0,
                role,
                kind,
                origin + range.start..origin + range.end,
            )];
            let mut fresh = None;
            for frozen in [None, Some(expected.as_slice())] {
                let mut output = frozen
                    .map(GreenNodeBuilder::reconcile)
                    .unwrap_or_else(GreenNodeBuilder::new);
                output.start_node(SyntaxKind::Root.into());
                let (mut exit, remainder) = parse_case_into(source, origin, None, &mut output);
                if let NormalizedExit::Complete(Err(Either::Right(end)), _) = &mut exit {
                    emit_end(&mut output, end);
                }
                output.finish_node();
                let (green, records) = output.finish_with_recoveries();
                assert_eq!(without_arm_records(&records), expected, "{source:?}");
                assert_eq!(
                    green.to_string(),
                    if role == Arm {
                        source.split('\n').next().unwrap()
                    } else {
                        source
                    },
                    "{source:?}"
                );
                assert_eq!(remainder, "");
                if let Some(fresh) = &fresh {
                    assert_eq!(&green, fresh);
                } else {
                    fresh = Some(green);
                }
            }
        }
        let seed = structural_record(7, Block, Missing, 0..0);
        let reused = structural_record(19, role, kind, 100 + range.start..100 + range.end);
        let frozen = [seed.clone(), reused.clone()];
        let mut output = GreenNodeBuilder::reconcile(&frozen);
        output.start_node(SyntaxKind::Root.into());
        output.start_node(SyntaxKind::Missing.into());
        output.finish_node();
        output.commit_recovery(crate::cst_output::RecoveryDraft::new(
            seed.site.clone(),
            seed.kind,
            seed.unexpected.clone(),
            seed.expectations.clone(),
            0,
        ));
        for origin in [100, 200] {
            let _ = parse_case_into(source, origin, None, &mut output);
        }
        output.finish_node();
        let (_, records) = output.finish_with_recoveries();
        let next_id = if matches!(source, "case x:" | "catch x: err," | "case x: @") {
            21
        } else {
            20
        };
        assert_eq!(
            without_arm_records(&records),
            [
                seed,
                reused,
                structural_record(next_id, role, kind, 200 + range.start..200 + range.end)
            ],
            "{source:?}"
        );
    }
}

fn expression(root: &SyntaxNode, kind: SyntaxKind) -> SyntaxNode {
    root.descendants()
        .find(|node| node.kind() == kind)
        .expect("case-like expression")
}

#[test]
fn case_arrow_body_records_are_exact_shifted_frozen_and_seeded() {
    use CaseLikeRole::{Arrow, Body};
    for (source, specifications) in [
        ("case x: n yes", vec![(Arrow, 10..10, false, vec![])]),
        ("case x: n ->", vec![(Body, 12..12, false, vec![])]),
        ("case x: n", vec![(Arrow, 9..9, true, vec![])]),
        ("case x: n if yes", vec![(Arrow, 16..16, true, vec![])]),
        ("case x: n  ", vec![(Arrow, 11..11, true, vec![])]),
        ("catch x: err, handler", vec![(Arrow, 21..21, true, vec![])]),
        (
            "catch x: err, handler ->",
            vec![(Body, 24..24, false, vec![])],
        ),
        (
            "catch x: err, handler yes",
            vec![(Arrow, 22..22, false, vec![])],
        ),
        (
            "case x: n @, _ -> b",
            vec![
                (Arrow, 10..10, false, vec![]),
                (Body, 10..11, false, vec![10..11]),
            ],
        ),
        (
            "case x: n -> @, _ -> b",
            vec![(Body, 13..14, false, vec![13..14])],
        ),
        (
            "case x: n -> @  ",
            vec![(Body, 13..14, false, vec![13..14])],
        ),
        (
            "case x: n -> @ \"yes\"",
            vec![(Body, 13..14, false, vec![13..14])],
        ),
        ("case x: n -> @;", vec![(Body, 13..14, false, vec![13..14])]),
        ("case x: n;", vec![(Arrow, 9..9, true, vec![])]),
        ("case x: n ->;", vec![(Body, 12..12, false, vec![])]),
        (
            "case α: n -> @ 💥 yes",
            vec![(Body, 14..20, false, vec![14..15, 15..20])],
        ),
    ] {
        let expected_at = |origin, first_id| {
            specifications
                .iter()
                .enumerate()
                .map(|(index, (role, range, combined, tokens))| {
                    let tokens: Vec<_> = tokens
                        .iter()
                        .map(|range| origin + range.start..origin + range.end)
                        .collect();
                    arm_record(
                        first_id + index as u32,
                        *role,
                        origin + range.start..origin + range.end,
                        *combined,
                        &tokens,
                    )
                })
                .collect::<Vec<_>>()
        };
        for origin in [0, 9100] {
            let expected = expected_at(origin, 0);
            let mut fresh = None;
            for frozen in [None, Some(expected.as_slice())] {
                let mut output = frozen
                    .map(GreenNodeBuilder::reconcile)
                    .unwrap_or_else(GreenNodeBuilder::new);
                output.start_node(SyntaxKind::Root.into());
                let (mut exit, remainder) = parse_case_into(source, origin, None, &mut output);
                if let NormalizedExit::Complete(Err(Either::Right(end)), _) = &mut exit {
                    emit_end(&mut output, end);
                }
                output.finish_node();
                let (green, records) = output.finish_with_recoveries();
                assert_eq!(records, expected, "{source:?}");
                assert_eq!(green.to_string(), source, "{source:?}");
                assert_eq!(remainder, "");
                if let Some(fresh) = &fresh {
                    assert_eq!(&green, fresh);
                } else {
                    fresh = Some(green);
                }
            }
        }
        let seed = structural_record(7, CaseLikeRole::Block, RecoveryKind::Missing, 0..0);
        let mut frozen = vec![seed.clone()];
        frozen.extend(expected_at(100, 19));
        let mut output = GreenNodeBuilder::reconcile(&frozen);
        output.start_node(SyntaxKind::Root.into());
        output.start_node(SyntaxKind::Missing.into());
        output.finish_node();
        output.commit_recovery(crate::cst_output::RecoveryDraft::new(
            seed.site.clone(),
            seed.kind,
            seed.unexpected.clone(),
            seed.expectations.clone(),
            0,
        ));
        for origin in [100, 200] {
            let _ = parse_case_into(source, origin, None, &mut output);
        }
        output.finish_node();
        let (_, records) = output.finish_with_recoveries();
        frozen.extend(expected_at(200, 19 + specifications.len() as u32));
        assert_eq!(records, frozen, "{source:?}");
    }
}

#[test]
fn case_arrow_body_combined_absence_keeps_prior_owner_records_in_order() {
    for (source, role, kind, range, at) in [
        (
            "case x:",
            CaseLikeRole::Pattern,
            RecoveryKind::Missing,
            7..7,
            7,
        ),
        (
            "case x: @",
            CaseLikeRole::Pattern,
            RecoveryKind::Error,
            8..9,
            9,
        ),
        (
            "catch x: err,",
            CaseLikeRole::Handler,
            RecoveryKind::Missing,
            13..13,
            13,
        ),
        (
            "case x: n if",
            CaseLikeRole::Guard,
            RecoveryKind::Missing,
            12..12,
            12,
        ),
    ] {
        let mut prior = structural_record(0, role, kind, range);
        if role == CaseLikeRole::Guard {
            prior = arm_record(0, role, prior.site.range, false, &[]);
        }
        let expected = [prior, arm_record(1, CaseLikeRole::Arrow, at..at, true, &[])];
        for frozen in [None, Some(expected.as_slice())] {
            let mut output = frozen
                .map(GreenNodeBuilder::reconcile)
                .unwrap_or_else(GreenNodeBuilder::new);
            output.start_node(SyntaxKind::Root.into());
            let _ = parse_case_into(source, 0, None, &mut output);
            output.finish_node();
            let (green, records) = output.finish_with_recoveries();
            assert_eq!(records, expected, "{source:?}");
            assert_eq!(
                SyntaxNode::new_root(green)
                    .descendants()
                    .filter(|node| node.kind() == SyntaxKind::Missing)
                    .count(),
                if kind == RecoveryKind::Missing { 2 } else { 1 }
            );
        }
    }
}

#[test]
fn case_arrow_body_keeps_protected_boundaries_before_and_after_error() {
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
    for head in [
        "case x: n",
        "case x: n ->",
        "case x: n -> @",
        "catch x: err, handler ->",
        "catch x: err, handler -> @",
    ] {
        for suffix in [
            " ]tail",
            " [tail",
            "\r\nnext",
            "\r\n> > ```\r\nouter",
            "\r\n> foreign",
        ] {
            if head.starts_with("case") && suffix.starts_with(" [") {
                // Case's existing sequence owner admits this Item as the next Pattern.
                continue;
            }
            let source = format!("{head}{suffix}");
            let fenced = suffix.contains('>');
            let origin = 7200;
            let error = head.ends_with('@');
            let combined = !head.contains("->");
            let at = origin + head.len() + if fenced { 2 } else { 0 };
            let expected = if error {
                let start = origin + head.find('@').unwrap();
                arm_record(
                    0,
                    CaseLikeRole::Body,
                    start..start + 1,
                    false,
                    &[start..start + 1],
                )
            } else {
                arm_record(
                    0,
                    if combined {
                        CaseLikeRole::Arrow
                    } else {
                        CaseLikeRole::Body
                    },
                    at..at,
                    combined,
                    &[],
                )
            };
            for frozen in [None, Some(std::slice::from_ref(&expected))] {
                let mut output = frozen
                    .map(GreenNodeBuilder::reconcile)
                    .unwrap_or_else(GreenNodeBuilder::new);
                output.start_node(SyntaxKind::Root.into());
                let (exit, remainder) =
                    parse_case_into(&source, origin, fenced.then_some(&fence), &mut output);
                output.finish_node();
                let (green, records) = output.finish_with_recoveries();
                assert_eq!(records, [expected.clone()], "{source:?}");
                assert_eq!(green.to_string(), head, "{source:?}");
                let NormalizedExit::Complete(Err(Either::Left(mut item)), line) = exit else {
                    panic!("pending boundary {source:?}")
                };
                let successor = origin + source.len() - remainder.len();
                assert_eq!(
                    item.extent(successor).recovery_range().start,
                    origin + head.len(),
                    "{source:?}"
                );
                if fenced {
                    assert!(item.payload_view().is_boundary());
                    assert_eq!(remainder, suffix.strip_prefix("\r\n").unwrap());
                    assert_eq!(line, LineEntry::PhysicalStart);
                } else {
                    assert_eq!(
                        emit_pending_leading_text(&mut item),
                        if suffix.starts_with('\r') {
                            "\r\n"
                        } else {
                            " "
                        }
                    );
                    assert_eq!(
                        remainder,
                        if suffix.starts_with('\r') { "" } else { "tail" }
                    );
                    assert_eq!(line, LineEntry::InLine);
                }
            }
        }
    }
}

#[test]
fn case_body_lexical_retry_keeps_native_tokens_and_prefix_admission() {
    let operators = OperatorTable::from_declarations([
        OperatorDeclaration::new(
            "-",
            OperatorFixities::new().with_prefix(BindingPower::scalar(40)),
        ),
        OperatorDeclaration::new(
            "+",
            OperatorFixities::new().with_infix(BindingPower::scalar(20), BindingPower::scalar(21)),
        ),
    ])
    .unwrap();
    for source in ["case x: n -> + - yes", "case x: n -> + - @"] {
        let parsed = crate::source_file::parse_root_candidate(source, &operators, &[]);
        assert_eq!(parsed.green.to_string(), source);
        if source.ends_with('@') {
            // The judge also rejects `- @`: it stays in the same lexical Body run.
            assert_eq!(
                parsed.committed_recoveries,
                [arm_record(
                    0,
                    CaseLikeRole::Body,
                    13..18,
                    false,
                    &[13..14, 14..16, 16..18]
                )]
            );
            assert!(
                !SyntaxNode::new_root(parsed.green)
                    .descendants()
                    .any(|node| node.kind() == SyntaxKind::PrefixOperatorUse)
            );
            continue;
        }
        assert_eq!(
            parsed.committed_recoveries[0],
            arm_record(0, CaseLikeRole::Body, 13..14, false, &[13..14])
        );
        let root = SyntaxNode::new_root(parsed.green);
        assert!(
            root.descendants()
                .any(|node| node.kind() == SyntaxKind::PrefixOperatorUse)
        );
        let error = root
            .descendants()
            .find(|node| node.kind() == SyntaxKind::Error)
            .unwrap();
        assert_eq!(error.to_string(), "+");
        // The unchanged NUD judge rejects this infix-only spelling as a native Unknown.
        assert_eq!(error.first_token().unwrap().kind(), SyntaxKind::Unknown);
        assert_eq!(parsed.committed_recoveries.len(), 1);
    }
}

#[test]
fn case_body_unread_opener_reaches_the_existing_next_pattern_owner() {
    for head in ["case x: n", "case x: n ->", "case x: n -> @"] {
        let source = format!("{head} [tail] -> yes");
        let mut output = GreenNodeBuilder::new();
        output.start_node(SyntaxKind::Root.into());
        let _ = parse_case_into(&source, 0, None, &mut output);
        output.finish_node();
        let (green, records) = output.finish_with_recoveries();
        let root = SyntaxNode::new_root(green);
        let arms: Vec<_> = root
            .descendants()
            .filter(|node| node.kind() == SyntaxKind::CaseArm)
            .collect();
        assert_eq!(arms.len(), 2);
        assert_eq!(arms[0].to_string(), head.strip_prefix("case x: ").unwrap());
        assert!(arms[1].to_string().contains("[tail] -> yes"));
        let expected = if head.ends_with('@') {
            arm_record(0, CaseLikeRole::Body, 13..14, false, &[13..14])
        } else {
            let combined = !head.contains("->");
            arm_record(
                0,
                if combined {
                    CaseLikeRole::Arrow
                } else {
                    CaseLikeRole::Body
                },
                head.len()..head.len(),
                combined,
                &[],
            )
        };
        assert_eq!(records, [expected]);
    }
}

#[test]
fn case_structural_nested_owners_and_following_statements_keep_their_roles() {
    use crate::recovery_record::{PatternRole, TypeRole};
    for (source, nested_role) in [
        (
            "case x: n as -> a",
            GrammarRole::Pattern(PatternRole::AliasBinding),
        ),
        (
            "catch x: err, n as -> a",
            GrammarRole::Pattern(PatternRole::AliasBinding),
        ),
        (
            "case x: n | -> a",
            GrammarRole::Pattern(PatternRole::AlternationRhs),
        ),
        (
            "catch x: err, n | -> a",
            GrammarRole::Pattern(PatternRole::AlternationRhs),
        ),
        (
            "(case x: n : T::)",
            GrammarRole::Type(TypeRole::PathSegment),
        ),
        (
            "(catch x: err, n : T::)",
            GrammarRole::Type(TypeRole::PathSegment),
        ),
    ] {
        let mut output = GreenNodeBuilder::new();
        output.start_node(SyntaxKind::Root.into());
        let _ = parse_case_into(source, 0, None, &mut output);
        output.finish_node();
        let (_, records) = output.finish_with_recoveries();
        let records = without_arm_records(&records);
        assert_eq!(records.len(), 1, "{source:?}: {records:?}");
        assert_eq!(records[0].site.role, nested_role, "{source:?}");
        assert_eq!(records[0].kind, RecoveryKind::Missing);
    }
    let operators = OperatorTable::empty();
    // E12k retains its literal; the following Statement remains independently owned.
    for source in [
        "my value = case x:\nnext",
        "my value = case x:\nmy next = 1",
        "my value = catch x:\r\nmy next = 1",
    ] {
        let parsed = crate::source_file::parse_root_candidate(source, &operators, &[]);
        assert_eq!(parsed.green.to_string(), source);
        let at = source.find(['\r', '\n']).unwrap();
        let records: Vec<_> = parsed
            .committed_recoveries
            .iter()
            .filter(|record| matches!(record.site.role, GrammarRole::CaseLike(_)))
            .cloned()
            .collect();
        assert_eq!(
            records,
            [structural_record(
                0,
                CaseLikeRole::Arm,
                RecoveryKind::Missing,
                at..at
            )]
        );
        let root = SyntaxNode::new_root(parsed.green);
        let block = root
            .descendants()
            .find(|node| matches!(node.kind(), SyntaxKind::CaseBlock | SyntaxKind::CatchBlock))
            .unwrap();
        assert_eq!(block.to_string(), ":");
        if source.contains("my next") {
            assert_eq!(
                root.descendants()
                    .filter(|node| node.kind() == SyntaxKind::BindingStatement)
                    .count(),
                2
            );
        }
    }
}

#[test]
fn case_structural_accepted_arm_families_remain_recovery_free() {
    for source in [
        "case x:  n -> a, _ -> b",
        "catch x:  err, handler -> a",
        "catch x {  err, handler -> a }",
        "case x:\n  n -> a\n  _ -> b",
        "catch x:\n  err, handler -> a",
    ] {
        let mut output = GreenNodeBuilder::new();
        output.start_node(SyntaxKind::Root.into());
        let (mut exit, remainder) = parse_case_into(source, 0, None, &mut output);
        if let NormalizedExit::Complete(Err(Either::Right(end)), _) = &mut exit {
            emit_end(&mut output, end);
        }
        output.finish_node();
        let (green, records) = output.finish_with_recoveries();
        assert_eq!(green.to_string(), source);
        assert!(records.is_empty(), "{source:?}: {records:?}");
        assert_eq!(remainder, "");
    }
}

#[test]
fn case_structural_block_and_arm_keep_protected_items_and_foreign_prefix_coordinates() {
    use crate::lexical::yumark::{FenceOpener, FencePrefixPolicy};
    for (source, emitted, at, kind) in [
        ("case x ;", "case x ", 7, TokenKind::Semicolon),
        ("case x  ]", "case x", 6, TokenKind::RBracket),
        ("catch x  }", "catch x", 7, TokenKind::RBrace),
    ] {
        let mut output = GreenNodeBuilder::new();
        output.start_node(SyntaxKind::Root.into());
        let (exit, remainder) = parse_case_into(source, 200, None, &mut output);
        output.finish_node();
        let (green, records) = output.finish_with_recoveries();
        assert_eq!(green.to_string(), emitted);
        assert_eq!(
            records,
            [structural_record(
                0,
                CaseLikeRole::Block,
                RecoveryKind::Missing,
                200 + at..200 + at
            )]
        );
        let NormalizedExit::Complete(Err(Either::Left(item)), _) = exit else {
            panic!("pending block boundary")
        };
        assert_eq!(token_kind(&item), Some(kind));
        assert_eq!(
            item.extent(200 + source.len() - remainder.len())
                .recovery_range()
                .start,
            200 + at
        );
    }
    let fence = FenceBoundary {
        opener: FenceOpener {
            line: 0,
            marker: 0..3,
            marker_width: 3,
        },
        prefix_policy: FencePrefixPolicy::ActivePrefixQuote { depth: 2, base: 0 },
        close_column: 0,
    };
    for (head, role, error) in [
        ("case α: @", CaseLikeRole::Pattern, true),
        ("catch α: err,", CaseLikeRole::Handler, false),
        ("catch α: err, @", CaseLikeRole::Handler, true),
    ] {
        let source = format!("{head}\r\n> > ```\r\nouter");
        let range = if error {
            head.find(',')
                .map_or_else(|| head.find('@').unwrap(), |comma| comma + 1)..head.len()
        } else {
            head.len() + 2..head.len() + 2
        };
        let expected = [structural_record(
            0,
            role,
            if error {
                RecoveryKind::Error
            } else {
                RecoveryKind::Missing
            },
            7000 + range.start..7000 + range.end,
        )];
        for frozen in [None, Some(expected.as_slice())] {
            let mut output = frozen
                .map(GreenNodeBuilder::reconcile)
                .unwrap_or_else(GreenNodeBuilder::new);
            output.start_node(SyntaxKind::Root.into());
            let (exit, remainder) = parse_case_into(&source, 7000, Some(&fence), &mut output);
            output.finish_node();
            let (green, records) = output.finish_with_recoveries();
            assert_eq!(without_arm_records(&records), expected, "{source:?}");
            assert_eq!(green.to_string(), head);
            let NormalizedExit::Complete(Err(Either::Left(item)), _) = exit else {
                panic!("fence remains pending")
            };
            assert!(item.payload_view().is_boundary());
            assert_eq!(
                item.extent(7000 + source.len() - remainder.len())
                    .recovery_range()
                    .start,
                7000 + head.len()
            );
            assert_eq!(remainder, "> > ```\r\nouter");
        }
    }
    for head in ["case α", "catch α", "case α:", "catch α:"] {
        for suffix in [
            "\r\nnext tail",
            "\nnext tail",
            "\r\n> > ```\r\nouter",
            "\r\n> foreign tail",
        ] {
            let fenced = suffix.contains('>');
            let source = format!("{head}{suffix}");
            let role = if head.ends_with(':') && !fenced {
                CaseLikeRole::Arm
            } else if head.ends_with(':') {
                CaseLikeRole::Pattern
            } else {
                CaseLikeRole::Block
            };
            let origin = 7000;
            let at = origin + head.len() + if fenced { 2 } else { 0 };
            let expected = [structural_record(0, role, RecoveryKind::Missing, at..at)];
            for frozen in [None, Some(expected.as_slice())] {
                let mut output = frozen
                    .map(GreenNodeBuilder::reconcile)
                    .unwrap_or_else(GreenNodeBuilder::new);
                output.start_node(SyntaxKind::Root.into());
                let (exit, remainder) =
                    parse_case_into(&source, origin, fenced.then_some(&fence), &mut output);
                output.finish_node();
                let (green, records) = output.finish_with_recoveries();
                assert_eq!(without_arm_records(&records), expected, "{source:?}");
                assert_eq!(green.to_string(), head, "{source:?}");
                let NormalizedExit::Complete(Err(Either::Left(mut item)), _) = exit else {
                    panic!("protected Item {source:?}")
                };
                let successor = origin + source.len() - remainder.len();
                assert_eq!(
                    item.extent(successor).recovery_range().start,
                    origin + head.len()
                );
                if fenced {
                    assert!(item.payload_view().is_boundary());
                } else {
                    assert_eq!(item.payload_view().spelling(), Some("next"));
                    assert_eq!(
                        emit_pending_leading_text(&mut item),
                        if suffix.starts_with("\r") {
                            "\r\n"
                        } else {
                            "\n"
                        }
                    );
                    assert_eq!(remainder, " tail");
                }
            }
        }
    }
    for source in ["(case α  )", "(catch α  )"] {
        let mut output = GreenNodeBuilder::new();
        output.start_node(SyntaxKind::Root.into());
        let (mut exit, remainder) = parse_case_into(source, 0, None, &mut output);
        if let NormalizedExit::Complete(Err(Either::Right(end)), _) = &mut exit {
            emit_end(&mut output, end);
        } else {
            panic!("outer close consumed");
        }
        output.finish_node();
        let (green, records) = output.finish_with_recoveries();
        let at = source.find("  )").unwrap();
        assert_eq!(
            records,
            [structural_record(
                0,
                CaseLikeRole::Block,
                RecoveryKind::Missing,
                at..at
            )]
        );
        assert_eq!(green.to_string(), source);
        assert_eq!(remainder, "");
        let root = SyntaxNode::new_root(green);
        let block = root
            .descendants()
            .find(|node| matches!(node.kind(), SyntaxKind::CaseBlock | SyntaxKind::CatchBlock))
            .unwrap();
        assert_eq!(block.to_string(), "");
        assert!(
            root.descendants_with_tokens()
                .filter_map(|e| e.into_token())
                .any(|t| t.kind() == SyntaxKind::RParen)
        );
    }
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
