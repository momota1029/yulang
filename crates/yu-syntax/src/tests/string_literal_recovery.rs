use crate::tests::support::*;
use crate::{
    ambient_claim::AmbientClaimView,
    handoff::MlMode,
    lexical::yumark::{FenceOpener, FencePrefixPolicy},
    literal::{scan_string_opener_witness, string_literal_with_virtual_statements_normalized},
    pattern::pattern_normalized,
    recovery_record::{
        Delimiter, DiagnosticId, ExpectationSources, ExpectedSyntax, GrammarRole, LiteralExpected,
        LiteralRole, PunctuationEvidence, RecoveryKind, RecoverySiteKey, SyntaxExpectation,
        UnexpectedCategory, UnexpectedSyntax,
    },
    statement::StatementLineHandoff,
};
use std::{ops::Range, sync::Arc};

fn record(
    id: u32,
    role: LiteralRole,
    kind: RecoveryKind,
    range: Range<usize>,
) -> CommittedRecoveryRecord {
    let expected = match role {
        LiteralRole::StringTerminator => ExpectedSyntax::Literal(LiteralExpected::StringTerminator),
        LiteralRole::StringEscapeSimpleTarget => {
            ExpectedSyntax::Literal(LiteralExpected::StringEscapeTarget)
        }
        LiteralRole::StringEscapeUnicodeHex => {
            ExpectedSyntax::Literal(LiteralExpected::UnicodeHexDigit)
        }
        LiteralRole::StringEscapeUnicodeEnd | LiteralRole::StringInterpolationCloseBrace => {
            ExpectedSyntax::Punctuation(PunctuationEvidence::Close(Delimiter::Brace))
        }
        LiteralRole::StringInterpolationOpenBrace => {
            ExpectedSyntax::Punctuation(PunctuationEvidence::Open(Delimiter::Brace))
        }
        _ => unreachable!(),
    };
    let role = GrammarRole::Literal(role);
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

fn parse<'s>(
    source: &'s str,
    origin: usize,
    fence: Option<&FenceBoundary>,
    frozen: Option<&[CommittedRecoveryRecord]>,
) -> (GreenNode, Vec<CommittedRecoveryRecord>, &'s str) {
    let operators = OperatorTable::empty();
    let mut recover = Recover::new(&operators);
    let mut input = source;
    let (opener, mode) = scan_string_opener_witness(In::new(&mut input, &mut recover, ())).unwrap();
    let mut output = frozen
        .map(GreenNodeBuilder::reconcile)
        .unwrap_or_else(GreenNodeBuilder::new);
    output.start_node(SyntaxKind::Root.into());
    let part_origin = origin + source.len() - input.len();
    string_literal_with_virtual_statements_normalized(
        In::new(&mut input, &mut recover, &mut output),
        opener,
        mode,
        part_origin,
        fence,
        Some(AmbientClaimView::root_statement(0)).into(),
    );
    output.finish_node();
    let (green, records) = output.finish_with_recoveries();
    (green, records, input)
}

#[test]
fn all_string_slots_have_exact_fresh_shifted_and_frozen_records() {
    use LiteralRole::*;
    use RecoveryKind::{Error, Missing};
    for (source, slots) in [
        ("\"α", vec![(StringTerminator, Missing, 3..3)]),
        ("\"\"\"α", vec![(StringTerminator, Missing, 5..5)]),
        ("\"\\\"", vec![(StringEscapeSimpleTarget, Missing, 2..2)]),
        (
            "\"\\",
            vec![
                (StringEscapeSimpleTarget, Missing, 2..2),
                (StringTerminator, Missing, 2..2),
            ],
        ),
        ("\"\\u{}\"", vec![(StringEscapeUnicodeHex, Missing, 4..4)]),
        (
            "\"\\u{\"",
            vec![
                (StringEscapeUnicodeHex, Missing, 4..4),
                (StringEscapeUnicodeEnd, Missing, 4..4),
            ],
        ),
        ("\"\\u{12\"", vec![(StringEscapeUnicodeEnd, Missing, 6..6)]),
        ("\"\\u{💥}\"", vec![(StringEscapeUnicodeHex, Error, 4..8)]),
        (
            "\"\\u{12💥\"",
            vec![
                (StringEscapeUnicodeHex, Error, 6..10),
                (StringEscapeUnicodeEnd, Missing, 10..10),
            ],
        ),
        (
            "\"\\u{💥",
            vec![
                (StringEscapeUnicodeHex, Error, 4..8),
                (StringEscapeUnicodeEnd, Missing, 8..8),
                (StringTerminator, Missing, 8..8),
            ],
        ),
        (
            "\"%fmt",
            vec![
                (StringInterpolationOpenBrace, Missing, 5..5),
                (StringTerminator, Missing, 5..5),
            ],
        ),
        (
            "\"%{",
            vec![
                (StringInterpolationCloseBrace, Missing, 3..3),
                (StringTerminator, Missing, 3..3),
            ],
        ),
        (
            "\"\\u{💥%{}\"",
            vec![
                (StringEscapeUnicodeHex, Error, 4..8),
                (StringEscapeUnicodeEnd, Missing, 8..8),
            ],
        ),
    ] {
        for origin in [0, 137] {
            let expected: Vec<_> = slots
                .iter()
                .enumerate()
                .map(|(id, (role, kind, range))| {
                    record(
                        id as u32,
                        *role,
                        *kind,
                        origin + range.start..origin + range.end,
                    )
                })
                .collect();
            let (green, records, remainder) = parse(source, origin, None, None);
            assert_eq!(green.to_string(), source, "{source:?}");
            assert_eq!(remainder, "");
            assert_eq!(records, expected, "{source:?}");
            let (again, frozen, remainder) = parse(source, origin, None, Some(&records));
            assert_eq!(again, green);
            assert_eq!(frozen, records);
            assert_eq!(remainder, "");
        }
    }
}

#[test]
fn valid_unicode_and_escaped_physical_lines_do_not_publish_recovery() {
    for source in [
        "\"\"",
        "\"\\u{123a}\"",
        "\"\\λ\"",
        "\"\\\nα\"",
        "\"\\\r\nα\"",
        "\"\"\"α\"\"\"",
    ] {
        let (green, records, remainder) = parse(source, 91, None, None);
        assert_eq!(green.to_string(), source);
        assert!(records.is_empty(), "{source:?}");
        assert_eq!(remainder, "");
    }
}

fn fence() -> FenceBoundary {
    FenceBoundary {
        opener: FenceOpener {
            line: 0,
            marker: 0..3,
            marker_width: 3,
        },
        prefix_policy: FencePrefixPolicy::ActivePrefixQuote { depth: 1, base: 0 },
        close_column: 0,
    }
}

#[test]
fn unicode_foreign_prefix_extent_and_deferred_structural_prefix_are_distinct() {
    use LiteralRole::*;
    use RecoveryKind::{Error, Missing};
    for (source, end, missing_end) in [
        ("\"\\u{💥\r\n> λ}\"", 14, false),
        ("\"\\u{💥\r\n> }\"", 10, false),
        ("\"\\u{💥\r\n> \"", 10, true),
        ("\"\\u{💥\r\n> %{}\"", 10, true),
    ] {
        let (green, records, remainder) = parse(source, 100, Some(&fence()), None);
        let mut expected = vec![record(0, StringEscapeUnicodeHex, Error, 104..100 + end)];
        if missing_end {
            expected.push(record(
                1,
                StringEscapeUnicodeEnd,
                Missing,
                100 + end..100 + end,
            ));
        }
        assert_eq!(records, expected, "{source:?}");
        assert_eq!(green.to_string(), source);
        assert_eq!(remainder, "");
        let root = SyntaxNode::new_root(green.clone());
        let error = root
            .descendants()
            .find(|node| node.kind() == SyntaxKind::Error)
            .unwrap();
        assert_eq!(error.to_string(), &source[4..end]);
        let (again, frozen, _) = parse(source, 100, Some(&fence()), Some(&records));
        assert_eq!(again, green);
        assert_eq!(frozen, records);
    }
}

#[test]
fn fence_boundaries_keep_remainder_and_order_string_records() {
    use LiteralRole::*;
    use RecoveryKind::{Error, Missing};
    for (body, slots) in [
        ("\"α\r\n", vec![(StringTerminator, Missing, 5..5)]),
        ("\"\"\"α\r\n", vec![(StringTerminator, Missing, 7..7)]),
        (
            "\"\\u{💥\r\n",
            vec![
                (StringEscapeUnicodeHex, Error, 4..10),
                (StringEscapeUnicodeEnd, Missing, 10..10),
                (StringTerminator, Missing, 10..10),
            ],
        ),
        (
            "\"%fmt\r\n",
            vec![
                (StringInterpolationOpenBrace, Missing, 7..7),
                (StringTerminator, Missing, 7..7),
            ],
        ),
        (
            "\"%{\r\n",
            vec![
                (StringInterpolationCloseBrace, Missing, 5..5),
                (StringTerminator, Missing, 5..5),
            ],
        ),
    ] {
        let source = format!("{body}> ```\nouter");
        let (green, records, remainder) = parse(&source, 200, Some(&fence()), None);
        let expected: Vec<_> = slots
            .iter()
            .enumerate()
            .map(|(id, (role, kind, range))| {
                record(id as u32, *role, *kind, 200 + range.start..200 + range.end)
            })
            .collect();
        assert_eq!(records, expected, "{source:?}");
        assert_eq!(remainder, "> ```\nouter");
        let (again, frozen, next) = parse(&source, 200, Some(&fence()), Some(&records));
        assert_eq!(again, green);
        assert_eq!(frozen, records);
        assert_eq!(next, remainder);
    }
}

#[test]
fn actual_expression_pattern_and_rule_string_callers_publish_literal_roles() {
    for (source, pattern, at) in [
        ("\"\\u{}\"", false, 4),
        ("\"\"\"\\u{}\"\"\"", true, 6),
        ("~\"{a=\"\\u{}\"}\"", false, 9),
    ] {
        let operators = OperatorTable::empty();
        let mut recover = Recover::new(&operators);
        let mut input = source;
        let mut output = GreenNodeBuilder::new();
        output.start_node(SyntaxKind::Root.into());
        if pattern {
            pattern_normalized(
                In::new(&mut input, &mut recover, &mut output),
                0,
                LineEntry::InLine,
                None,
                0,
                Some(AmbientClaimView::root_statement(0)).into(),
            );
        } else {
            assert!(
                expr_normalized(
                    In::new(&mut input, &mut recover, &mut output),
                    None,
                    0,
                    0,
                    MlMode::All,
                    StatementLineHandoff::OrdinaryLayout,
                    0,
                    LineEntry::InLine,
                    None,
                    Some(AmbientClaimView::root_statement(0)).into(),
                    None
                )
                .is_some()
            );
        }
        output.finish_node();
        let (green, records) = output.finish_with_recoveries();
        assert_eq!(green.to_string(), source);
        assert_eq!(input, "");
        assert_eq!(
            records,
            [record(
                0,
                LiteralRole::StringEscapeUnicodeHex,
                RecoveryKind::Missing,
                at..at
            )]
        );
    }
}

#[test]
fn rejected_opener_is_effect_free() {
    let operators = OperatorTable::empty();
    let mut recover = Recover::new(&operators);
    let mut input = "α";
    let mut output = GreenNodeBuilder::new();
    output.start_node(SyntaxKind::Root.into());
    output.token(SyntaxKind::Identifier.into(), "seed");
    assert!(scan_string_opener_witness(In::new(&mut input, &mut recover, ())).is_none());
    assert_eq!(input, "α");
    assert_eq!(output.recovery_slot_count(), 0);
    output.finish_node();
    assert_eq!(output.finish_with_recoveries().0.to_string(), "seed");
}

#[test]
fn literal_recovery_preserves_seeded_ids_and_allocates_after_frozen_records() {
    use crate::cst_output::RecoveryDraft;
    let seed = record(
        7,
        LiteralRole::StringTerminator,
        RecoveryKind::Missing,
        0..0,
    );
    let reused = record(
        19,
        LiteralRole::StringEscapeUnicodeHex,
        RecoveryKind::Missing,
        14..14,
    );
    let frozen = [seed.clone(), reused.clone()];
    for reconcile in [false, true] {
        let operators = OperatorTable::empty();
        let mut recover = Recover::new(&operators);
        let mut output = if reconcile {
            GreenNodeBuilder::reconcile(&frozen)
        } else {
            GreenNodeBuilder::new()
        };
        output.start_node(SyntaxKind::Root.into());
        output.token(SyntaxKind::Identifier.into(), "seed");
        output.start_node(SyntaxKind::Missing.into());
        output.finish_node();
        output.commit_recovery(RecoveryDraft::new(
            seed.site.clone(),
            seed.kind,
            seed.unexpected.clone(),
            seed.expectations.clone(),
            0,
        ));
        for origin in [10, 20] {
            let mut input = "\"\\u{}\"";
            let (opener, mode) =
                scan_string_opener_witness(In::new(&mut input, &mut recover, ())).unwrap();
            string_literal_with_virtual_statements_normalized(
                In::new(&mut input, &mut recover, &mut output),
                opener,
                mode,
                origin + 1,
                None,
                Some(AmbientClaimView::root_statement(0)).into(),
            );
            assert_eq!(input, "");
        }
        output.finish_node();
        let (green, records) = output.finish_with_recoveries();
        assert_eq!(green.to_string(), "seed\"\\u{}\"\"\\u{}\"");
        assert_eq!(
            records,
            [
                record(
                    if reconcile { 7 } else { 0 },
                    LiteralRole::StringTerminator,
                    RecoveryKind::Missing,
                    0..0
                ),
                record(
                    if reconcile { 19 } else { 1 },
                    LiteralRole::StringEscapeUnicodeHex,
                    RecoveryKind::Missing,
                    14..14
                ),
                record(
                    if reconcile { 20 } else { 2 },
                    LiteralRole::StringEscapeUnicodeHex,
                    RecoveryKind::Missing,
                    24..24
                ),
            ]
        );
    }
}

#[test]
fn interpolation_child_recovery_precedes_close_and_terminator_without_relabeling() {
    let (green, records, remainder) = parse("\"%{  ", 100, None, None);
    assert_eq!(green.to_string(), "\"%{");
    assert_eq!(remainder, "");
    assert_eq!(
        records,
        [
            record(
                0,
                LiteralRole::StringInterpolationCloseBrace,
                RecoveryKind::Missing,
                105..105
            ),
            record(
                1,
                LiteralRole::StringTerminator,
                RecoveryKind::Missing,
                105..105
            ),
        ]
    );
    let (again, frozen, _) = parse("\"%{  ", 100, None, Some(&records));
    assert_eq!(again, green);
    assert_eq!(frozen, records);
    let (green, records, _) = parse("\"%{,", 0, None, None);
    assert_eq!(
        records,
        [
            record(
                0,
                LiteralRole::StringInterpolationCloseBrace,
                RecoveryKind::Missing,
                4..4
            ),
            record(
                1,
                LiteralRole::StringTerminator,
                RecoveryKind::Missing,
                4..4
            )
        ]
    );
    let root = SyntaxNode::new_root(green);
    let missing: Vec<_> = root
        .descendants()
        .filter(|node| node.kind() == SyntaxKind::Missing)
        .map(|node| node.parent().unwrap().kind())
        .collect();
    assert_eq!(
        missing,
        [
            SyntaxKind::Statement,
            SyntaxKind::StringInterpolation,
            SyntaxKind::StringLiteral
        ]
    );
    let source = "\"%{x \t}tail\"";
    let (green, records, remainder) = parse(source, 0, None, None);
    assert!(records.is_empty());
    assert_eq!(green.to_string(), source);
    assert_eq!(remainder, "");
    let root = SyntaxNode::new_root(green);
    let body = root
        .descendants()
        .find(|node| node.kind() == SyntaxKind::StringInterpolationBody)
        .unwrap();
    assert_eq!(body.to_string(), "x");
    assert_eq!(
        root.descendants_with_tokens()
            .filter(|element| element.kind() == SyntaxKind::StringInterpolationCloseBrace)
            .count(),
        1
    );
}
