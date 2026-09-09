use crate::recovery_record::{ColonApplicationRole, GrammarRole, RecoveryKind};
use crate::tests::support::*;
use crate::{
    ambient_claim::AmbientClaimView,
    handoff::MlMode,
    sequence::{SequenceContext, SequenceOwner},
    statement::StatementLineHandoff,
};

fn parse<'s>(
    source: &'s str,
    sequence: SequenceContext,
    origin: usize,
    frozen: Option<&[CommittedRecoveryRecord]>,
) -> (
    GreenNode,
    Vec<CommittedRecoveryRecord>,
    NormalizedExit,
    &'s str,
) {
    parse_fenced(source, sequence, origin, None, frozen)
}

fn parse_fenced<'s>(
    source: &'s str,
    sequence: SequenceContext,
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
    let exit = expr_normalized(
        crate::cursor::SyntaxIn::new(&mut input, &mut recover, &mut output),
        None,
        0,
        0,
        MlMode::All,
        StatementLineHandoff::OrdinaryLayout,
        origin,
        LineEntry::InLine,
        fence,
        Some(AmbientClaimView::root_statement(0)).into(),
        sequence,
    )
    .unwrap();
    output.finish_node();
    let (green, records) = (output.finish(), recover.finish_recoveries_for_test());
    (green, records, exit, input)
}

fn arguments(green: &GreenNode) -> Vec<usize> {
    SyntaxNode::new_root(green.clone())
        .descendants()
        .filter(|n| n.kind() == SyntaxKind::ColonApplicationTail)
        .map(|n| {
            n.children()
                .filter(|n| n.kind() == SyntaxKind::OperatorChain)
                .count()
        })
        .collect()
}

#[test]
fn ownerless_colon_owns_comma_and_layout_newline_episodes() {
    for source in [
        "f: a, b",
        "f: a\nb",
        "f: a,\nb",
        "f: a\n, b",
        "f: a\n,\nb",
        "f: a\r\nb",
    ] {
        let (green, records, _, rest) = parse(source, None, 0, None);
        assert_eq!(green.to_string(), source, "{source:?}");
        assert_eq!(arguments(&green), [2], "{source:?}");
        assert!(records.is_empty(), "{source:?}: {records:?}");
        assert_eq!(rest, "");
    }
    let (green, records, _, _) = parse("f: a\n  b", None, 0, None);
    assert_eq!(arguments(&green), [1]);
    assert!(records.is_empty());
}

#[test]
fn every_explicit_owner_returns_the_whole_outer_comma_and_newline_item() {
    use SequenceOwner::*;
    for owner in [
        RootStatement,
        VirtualStatement,
        RecordPattern,
        RuleExpressionList,
        Parenthesized,
        Call,
        Index,
        ProjectionTuple,
        ProjectionRecord,
        Colon,
        IndentedStatement,
        BracedStatement,
        CaseInline,
        CaseIndented,
        CatchInline,
        CatchIndented,
        CatchBraced,
        If,
    ] {
        for (source, kind, range, rest) in [
            ("f: a , b", TokenKind::Comma, 4..6, " b"),
            ("f: a\r\n界", TokenKind::Identifier, 4..9, ""),
        ] {
            let (green, records, exit, remaining) = parse(source, Some(owner), 0, None);
            assert_eq!(green.to_string(), "f: a", "{owner:?} {source:?}");
            assert_eq!(arguments(&green), [1]);
            assert!(records.is_empty());
            let NormalizedExit::Complete(Err(Either::Left(item)), _) = exit else {
                panic!("whole pending Item")
            };
            assert_eq!(token_kind(&item), Some(kind));
            assert_eq!(
                item.extent(source.len() - remaining.len()).recovery_range(),
                range
            );
            assert_eq!(remaining, rest);
        }
    }
}

#[test]
fn accepted_delimiters_replace_and_restore_the_callers_sequence() {
    for source in [
        "(f: a\nb)",
        "g(f: a\nb)",
        "g[f: a\nb]",
        "g.(f: a\nb)",
        "g.{f: a\nb}",
    ] {
        let (green, records, _, _) = parse(source, None, 0, None);
        assert_eq!(green.to_string(), source, "{source:?}");
        assert_eq!(arguments(&green), [1], "{source:?}");
        assert!(records.is_empty(), "{source:?}: {records:?}");
    }
    for (source, counts) in [
        ("(x): a, b", vec![2]),
        ("f: g: a, b", vec![2, 1]),
        ("f: (g: a, b), c", vec![2, 1]),
    ] {
        let (green, records, _, _) = parse(source, None, 0, None);
        assert_eq!(green.to_string(), source);
        assert_eq!(arguments(&green), counts);
        assert!(records.is_empty());
    }
}

#[test]
fn immediate_post_colon_newline_precedes_local_comma_recovery() {
    for source in ["f:\n, x", "f:\r\nx"] {
        let (green, records, exit, remaining) = parse(source, None, 0, None);
        assert_eq!(green.to_string(), "f:");
        assert_eq!(records.len(), 1);
        assert_eq!(
            records[0].site.role,
            GrammarRole::ColonApplication(ColonApplicationRole::Rhs)
        );
        assert_eq!(records[0].site.range, 2..2);
        assert_eq!(records[0].kind, RecoveryKind::Missing);
        let NormalizedExit::Complete(Err(Either::Left(item)), _) = exit else {
            panic!("pending newline Item")
        };
        assert_eq!(
            item.extent(source.len() - remaining.len())
                .recovery_range()
                .start,
            2
        );
        assert!(item.leading_view().has_ordinary_newline());
    }
    let (green, records, _, _) = parse("f:\n  a\n  b", None, 0, None);
    assert_eq!(green.to_string(), "f:\n  a\n  b");
    assert!(records.is_empty());
}

#[test]
fn lexical_error_retry_obeys_owned_and_protected_boundaries_in_frozen_output() {
    for (source, sequence, text) in [
        ("f: @\r\n界", None, "f: @\r\n界"),
        ("f: @, x", None, "f: @, x"),
        ("f: @\r\n界", Some(SequenceOwner::RootStatement), "f: @"),
        ("f: @, x", Some(SequenceOwner::RootStatement), "f: @"),
        ("f: @ ]", None, "f: @"),
    ] {
        let (green, records, _, _) = parse(source, sequence, 40, None);
        assert_eq!(green.to_string(), text, "{source:?}");
        assert_eq!(records.len(), 1);
        assert_eq!(records[0].kind, RecoveryKind::Error);
        assert_eq!(records[0].site.range, 43..44);
        let (frozen_green, frozen_records, _, _) = parse(source, sequence, 40, Some(&records));
        assert_eq!(frozen_green, green);
        assert_eq!(frozen_records, records);
    }
}

#[test]
fn actual_virtual_interpolation_has_outer_colon_sequence_ownership() {
    for interior in [
        "f: a, b", "f: a\nb", "f: a; b", "f: a", "f: @, b", "f: @\nb",
    ] {
        for quote in ["\"", "\"\"\""] {
            let source = format!("{quote}%{{{interior}}}後{quote}");
            let (green, _, _, rest) = parse(&source, None, 0, None);
            assert_eq!(green.to_string(), source);
            assert_eq!(
                arguments(&green),
                if interior.contains('@') {
                    vec![0]
                } else {
                    vec![1]
                }
            );
            assert_eq!(rest, "");
        }
    }
}

#[test]
fn actual_statement_if_and_arm_owners_keep_colon_to_one_argument() {
    for source in [
        "{f: a\nb}",
        "case x: n -> f: a, m -> b",
        "case x:\n  n -> f: a\n  m -> b",
        "catch x: n -> f: a",
        "catch x:\n  n -> f: a\n  m -> b",
        "catch x {n -> f: a, m -> b}",
        "if x: f: a else: g: b",
    ] {
        let (green, records, _, _) = parse(source, None, 0, None);
        assert_eq!(green.to_string(), source, "{source:?}");
        assert!(arguments(&green).iter().all(|n| *n == 1), "{source:?}");
        assert!(!arguments(&green).is_empty());
        assert!(records.is_empty(), "{source:?}: {records:?}");
    }
    let (green, records, _, _) = parse("g:\n  f: a\n  b", None, 0, None);
    assert_eq!(green.to_string(), "g:\n  f: a\n  b");
    assert_eq!(arguments(&green), [0, 1]);
    assert!(records.is_empty());
    let (green, exit) = run_statement("f: a, b");
    assert_eq!(green.to_string(), "f: a");
    assert_eq!(arguments(&green), [1]);
    assert!(matches!(exit, Some(Err(Either::Left(_)))));
}

#[test]
fn record_pattern_defaults_establish_their_local_expression_owner() {
    for source in ["{x = f: a, y}", "{x = f: a\ny}", "{x = (f: a, b), y}"] {
        let (green, _) = run_pattern(source);
        assert_eq!(green.to_string(), source, "{source:?}");
        assert_eq!(arguments(&green), [1]);
        assert!(
            !SyntaxNode::new_root(green)
                .descendants()
                .any(|n| matches!(n.kind(), SyntaxKind::Missing | SyntaxKind::Error))
        );
    }
}

#[test]
fn trailing_literal_comma_and_repeated_comma_keep_mandatory_slots() {
    for source in ["f: a,", "f: a,, b"] {
        let (green, records, _, _) = parse(source, None, 0, None);
        assert_eq!(green.to_string(), source);
        assert_eq!(records.len(), 1, "{source:?}");
        assert_eq!(records[0].kind, RecoveryKind::Missing);
        assert_eq!(
            records[0].site.role,
            GrammarRole::ColonApplication(ColonApplicationRole::InlineArgument)
        );
        let (again, frozen, _, _) = parse(source, None, 0, Some(&records));
        assert_eq!(again, green);
        assert_eq!(frozen, records);
    }
}

#[test]
fn trailing_implicit_boundary_preserves_trivia_without_a_missing_argument() {
    for source in ["f: a\n", "f: a\r\n", "f: @\n", "f: @\r\n"] {
        let (green, records, exit, remaining) = parse(source, None, 0, None);
        assert_eq!(green.to_string(), source);
        assert_eq!(remaining, "");
        assert!(matches!(
            exit,
            NormalizedExit::Complete(Err(Either::Right(_)), _)
        ));
        assert!(
            records
                .iter()
                .all(|record| record.kind == RecoveryKind::Error)
        );
        assert_eq!(records.len(), usize::from(source.contains('@')));
        let (again, frozen, _, _) = parse(source, None, 0, Some(&records));
        assert_eq!(again, green);
        assert_eq!(frozen, records);
    }
}

#[test]
fn nested_virtual_colons_replace_and_restore_virtual_and_outer_owners() {
    for quote in ["\"", "\"\"\""] {
        let source = format!("{quote}%{{\"%{{g: a, b}}\"; f: c, d}}{quote}: e, z");
        let (green, records, _, remaining) = parse(&source, None, 0, None);
        assert_eq!(green.to_string(), source);
        assert_eq!(remaining, "");
        assert!(records.is_empty());
        assert_eq!(arguments(&green), [1, 1, 2]);
        let (again, frozen, _, _) = parse(&source, None, 0, Some(&records));
        assert_eq!(again, green);
        assert_eq!(frozen, records);
    }
}

#[test]
fn virtual_colon_errors_keep_close_eof_and_quoted_fence_records_frozen() {
    use crate::lexical::yumark::{FenceOpener, FencePrefixPolicy};
    use crate::recovery_record::{
        Delimiter, DiagnosticId, ExpectationSources, ExpectedSyntax, LiteralExpected, LiteralRole,
        PunctuationEvidence, RecoverySiteKey, SyntaxExpectation, UnexpectedCategory,
        UnexpectedSyntax,
    };
    use std::sync::Arc;
    let fence = FenceBoundary {
        opener: FenceOpener {
            line: 0,
            marker: 0..3,
            marker_width: 3,
        },
        prefix_policy: FencePrefixPolicy::ActivePrefixQuote { depth: 2, base: 0 },
        close_column: 0,
    };
    for quote in ["\"", "\"\"\""] {
        for suffix in [
            format!(" }}後{quote}"),
            String::new(),
            "\r\n> > ```\nouter".to_owned(),
        ] {
            let source = format!("{quote}%{{f: 💥{suffix}");
            let (green, records, exit, remaining) =
                parse_fenced(&source, None, 80, Some(&fence), None);
            let start = 80 + quote.len() + "%{f: ".len();
            let role = GrammarRole::ColonApplication(ColonApplicationRole::Rhs);
            let mut expected = vec![CommittedRecoveryRecord {
                id: DiagnosticId(0),
                site: RecoverySiteKey {
                    role,
                    range: start..start + 4,
                },
                kind: RecoveryKind::Error,
                unexpected: Arc::from([UnexpectedSyntax::Token {
                    range: start..start + 4,
                    category: UnexpectedCategory::OtherCharacter,
                }]),
                expectations: Arc::from([SyntaxExpectation {
                    role,
                    expected: ExpectedSyntax::Expression,
                    range: start..start + 4,
                    sources: ExpectationSources::COMMITTED_RECOVERY_RULE,
                }]),
                primary_expectation: 0,
            }];
            if suffix.is_empty() || suffix.contains("```") {
                let at = start + if suffix.is_empty() { 4 } else { 6 };
                for (id, slot, expected_syntax) in [
                    (
                        1,
                        LiteralRole::StringInterpolationCloseBrace,
                        ExpectedSyntax::Punctuation(PunctuationEvidence::Close(Delimiter::Brace)),
                    ),
                    (
                        2,
                        LiteralRole::StringTerminator,
                        ExpectedSyntax::Literal(LiteralExpected::StringTerminator),
                    ),
                ] {
                    let role = GrammarRole::Literal(slot);
                    expected.push(CommittedRecoveryRecord {
                        id: DiagnosticId(id),
                        site: RecoverySiteKey {
                            role,
                            range: at..at,
                        },
                        kind: RecoveryKind::Missing,
                        unexpected: Arc::from([]),
                        expectations: Arc::from([SyntaxExpectation {
                            role,
                            expected: expected_syntax,
                            range: at..at,
                            sources: ExpectationSources::COMMITTED_RECOVERY_RULE,
                        }]),
                        primary_expectation: 0,
                    });
                }
            }
            assert_eq!(records, expected, "{source:?}");
            if suffix.contains("```") {
                assert_eq!(green.to_string(), format!("{quote}%{{f: 💥"));
                assert_eq!(remaining, "> > ```\nouter");
                let NormalizedExit::Complete(Err(Either::Left(item)), LineEntry::PhysicalStart) =
                    exit
                else {
                    panic!("pending physical fence")
                };
                assert!(item.payload_view().is_boundary());
            } else {
                assert_eq!(green.to_string(), source);
                assert_eq!(remaining, "");
            }
            let (again, frozen, _, _) =
                parse_fenced(&source, None, 80, Some(&fence), Some(&records));
            assert_eq!(again, green);
            assert_eq!(frozen, records);
        }
    }
}
