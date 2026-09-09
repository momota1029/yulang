use crate::tests::support::*;
use crate::{
    ambient_claim::AmbientClaimView,
    literal::{rule_literal_normalized, scan_expression_rule_literal_opener_witness},
    recovery_record::{
        Delimiter, DiagnosticId, ExpectationSources, ExpectedSyntax, GrammarRole, LiteralExpected,
        LiteralRole, PunctuationEvidence, RecoveryKind, RecoverySiteKey, SyntaxExpectation,
        UnexpectedCategory, UnexpectedSyntax,
    },
    rule::{rule_body_witness, scan_rule_current_item_witness, scan_rule_item_witness},
};
use std::{ops::Range, sync::Arc};

fn record(
    id: u32,
    role: LiteralRole,
    range: Range<usize>,
    category: Option<UnexpectedCategory>,
) -> CommittedRecoveryRecord {
    use LiteralRole::*;
    let expected = match role {
        RuleBodyCloseBrace | RuleLiteralInterpolationCloseBrace | RuleLazyCaptureCloseBrace => {
            ExpectedSyntax::Punctuation(PunctuationEvidence::Close(Delimiter::Brace))
        }
        RuleParenClose => {
            ExpectedSyntax::Punctuation(PunctuationEvidence::Close(Delimiter::Parenthesis))
        }
        RuleCaptureRightItem | RuleUnexpectedItem => {
            ExpectedSyntax::Literal(LiteralExpected::RuleItem)
        }
        RuleFieldName | RulePathName | RuleLazyCaptureName => ExpectedSyntax::Identifier,
        RuleLiteralTerminator => ExpectedSyntax::Literal(LiteralExpected::RuleLiteralTerminator),
        _ => unreachable!(),
    };
    let role = GrammarRole::Literal(role);
    CommittedRecoveryRecord {
        id: DiagnosticId(id),
        site: RecoverySiteKey {
            role,
            range: range.clone(),
        },
        kind: if category.is_some() {
            RecoveryKind::Error
        } else {
            RecoveryKind::Missing
        },
        unexpected: category.map_or_else(
            || Arc::from([]),
            |category| {
                Arc::from([UnexpectedSyntax::Token {
                    range: range.clone(),
                    category,
                }])
            },
        ),
        expectations: Arc::from([SyntaxExpectation {
            role,
            expected,
            range,
            sources: ExpectationSources::COMMITTED_RECOVERY_RULE,
        }]),
        primary_expectation: 0,
    }
}

fn parse(
    source: &str,
    origin: usize,
    frozen: Option<&[CommittedRecoveryRecord]>,
) -> (GreenNode, Vec<CommittedRecoveryRecord>) {
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
    if source.starts_with('{') {
        let opener = scan_rule_item_witness(chasa_recover::In::new(
            &mut input,
            &mut crate::cursor::LexRecover::new_for_test(recover.operators()),
            (),
        ))
        .unwrap();
        let current = scan_rule_current_item_witness(
            chasa_recover::In::new(
                &mut input,
                &mut crate::cursor::LexRecover::new_for_test(recover.operators()),
                (),
            ),
            origin + 1,
            LineEntry::InLine,
            None,
        );
        let end = origin + source.len() - input.len();
        rule_body_witness(
            crate::cursor::SyntaxIn::new(&mut input, &mut recover, &mut output),
            opener,
            current.item,
            current.next_line_entry,
            end,
            None,
        );
    } else {
        let opener = scan_expression_rule_literal_opener_witness(chasa_recover::In::new(
            &mut input,
            &mut crate::cursor::LexRecover::new_for_test(recover.operators()),
            (),
        ))
        .unwrap();
        rule_literal_normalized(
            crate::cursor::SyntaxIn::new(&mut input, &mut recover, &mut output),
            opener,
            origin + 2,
            LineEntry::InLine,
            None,
            Some(AmbientClaimView::root_statement(0)).into(),
        );
    }
    output.finish_node();
    (output.finish(), recover.finish_recoveries_for_test())
}

#[test]
fn all_ten_rule_roles_have_exact_shifted_and_frozen_records() {
    use LiteralRole::*;
    for (source, slots) in [
        ("{", vec![(RuleBodyCloseBrace, 1..1, None)]),
        ("{(}", vec![(RuleParenClose, 2..2, None)]),
        ("{a=}", vec![(RuleCaptureRightItem, 3..3, None)]),
        ("{a.}", vec![(RuleFieldName, 3..3, None)]),
        ("{a::}", vec![(RulePathName, 4..4, None)]),
        (
            "{a. 12 b}",
            vec![(
                RuleFieldName,
                3..6,
                Some(UnexpectedCategory::DecimalInteger),
            )],
        ),
        (
            "{a::💥 b}",
            vec![(RulePathName, 4..8, Some(UnexpectedCategory::OperatorLike))],
        ),
        (
            "{;💥}",
            vec![
                (
                    RuleUnexpectedItem,
                    1..2,
                    Some(UnexpectedCategory::Punctuation(
                        PunctuationEvidence::Semicolon,
                    )),
                ),
                (
                    RuleUnexpectedItem,
                    2..6,
                    Some(UnexpectedCategory::OperatorLike),
                ),
            ],
        ),
        ("~\"α", vec![(RuleLiteralTerminator, 4..4, None)]),
        (
            "~\"{a",
            vec![
                (RuleLiteralInterpolationCloseBrace, 4..4, None),
                (RuleLiteralTerminator, 4..4, None),
            ],
        ),
        ("~\":\"", vec![(RuleLazyCaptureName, 3..3, None)]),
        (
            "~\":{α",
            vec![
                (RuleLazyCaptureCloseBrace, 6..6, None),
                (RuleLiteralTerminator, 6..6, None),
            ],
        ),
        (
            "~\"{a  \"",
            vec![(RuleLiteralInterpolationCloseBrace, 6..6, None)],
        ),
    ] {
        for origin in [0, 137] {
            let expected: Vec<_> = slots
                .iter()
                .enumerate()
                .map(|(id, (role, range, category))| {
                    record(
                        id as u32,
                        *role,
                        origin + range.start..origin + range.end,
                        *category,
                    )
                })
                .collect();
            let (green, records) = parse(source, origin, None);
            assert_eq!(green.to_string(), source, "{source:?}");
            assert_eq!(records, expected, "{source:?}");
            let (again, frozen) = parse(source, origin, Some(&records));
            assert_eq!(again, green);
            assert_eq!(frozen, records);
        }
    }
}

#[test]
fn required_slots_stop_before_body_and_paren_newline_name_admission() {
    for (source, role, at) in [
        ("{a.\nnext}", LiteralRole::RuleFieldName, 3),
        ("{a::\nnext}", LiteralRole::RulePathName, 4),
        ("{a=\nnext}", LiteralRole::RuleCaptureRightItem, 3),
        ("{(a.\r\nnext)}", LiteralRole::RuleFieldName, 4),
        ("{(a::\r\nnext)}", LiteralRole::RulePathName, 5),
        ("{(a=\r\nnext)}", LiteralRole::RuleCaptureRightItem, 4),
    ] {
        let (green, records) = parse(source, 0, None);
        assert_eq!(green.to_string(), source);
        assert_eq!(records, [record(0, role, at..at, None)], "{source:?}");
    }
}

#[test]
fn eof_leading_stays_pending_while_nested_missing_uses_successor_coordinate() {
    use LiteralRole::*;
    for (source, emitted, roles) in [
        (
            "{a=  ",
            "{a=",
            vec![RuleCaptureRightItem, RuleBodyCloseBrace],
        ),
        (
            "{a:: /*gap*/",
            "{a::",
            vec![RulePathName, RuleBodyCloseBrace],
        ),
        (
            "{(a=  ",
            "{(a=",
            vec![RuleCaptureRightItem, RuleParenClose, RuleBodyCloseBrace],
        ),
        (
            "{(a:: /*α*/",
            "{(a::",
            vec![RulePathName, RuleParenClose, RuleBodyCloseBrace],
        ),
    ] {
        for origin in [0, 137] {
            let at = origin + source.len();
            let expected: Vec<_> = roles
                .iter()
                .enumerate()
                .map(|(id, role)| record(id as u32, *role, at..at, None))
                .collect();
            let (green, records) = parse(source, origin, None);
            assert_eq!(green.to_string(), emitted, "{source:?}");
            assert_eq!(records, expected, "{source:?}");
            let (again, frozen) = parse(source, origin, Some(&records));
            assert_eq!(again, green);
            assert_eq!(frozen, records);
        }
    }
}

#[test]
fn interpolation_retains_its_own_stops_and_one_item_errors() {
    let source = "~\"{| if ]}\"";
    let (green, records) = parse(source, 0, None);
    assert_eq!(green.to_string(), source);
    assert_eq!(
        records,
        [
            record(
                0,
                LiteralRole::RuleUnexpectedItem,
                3..4,
                Some(UnexpectedCategory::Punctuation(PunctuationEvidence::Pipe))
            ),
            record(
                1,
                LiteralRole::RuleUnexpectedItem,
                4..7,
                Some(UnexpectedCategory::Word)
            ),
            record(
                2,
                LiteralRole::RuleUnexpectedItem,
                7..9,
                Some(UnexpectedCategory::Punctuation(PunctuationEvidence::Close(
                    Delimiter::Bracket
                )))
            ),
        ]
    );
}

#[test]
fn accepted_alternatives_lazy_quantifiers_and_raw_capture_have_no_records() {
    for source in [
        "{a|\nb*?||c+?}",
        "{(a,,b,)}",
        "{a.x::y}",
        "~\"text:name :{} :{raw α}\"",
        "~\"{a=\"nested\"}\"",
    ] {
        let (green, records) = parse(source, 0, None);
        assert_eq!(green.to_string(), source);
        assert!(records.is_empty(), "{source:?}: {records:?}");
    }
}

#[test]
fn actual_expression_and_pattern_routes_publish_rule_records() {
    use crate::{handoff::MlMode, pattern::pattern_normalized, statement::StatementLineHandoff};
    for (source, pattern, role, at) in [
        ("~\":\"", false, LiteralRole::RuleLazyCaptureName, 3),
        ("\":\"", true, LiteralRole::RuleLazyCaptureName, 2),
        ("~\"{a.}\"", false, LiteralRole::RuleFieldName, 5),
        ("\"{a::}\"", true, LiteralRole::RulePathName, 5),
    ] {
        let operators = OperatorTable::empty();
        let mut recover = Recover::new_for_test(&operators);
        let mut input = source;
        let mut output = GreenNodeBuilder::new();
        output.start_node(SyntaxKind::Root.into());
        if pattern {
            pattern_normalized(
                crate::cursor::SyntaxIn::new(&mut input, &mut recover, &mut output),
                0,
                LineEntry::InLine,
                None,
                0,
                Some(AmbientClaimView::root_statement(0)).into(),
            );
        } else {
            assert!(
                expr_normalized(
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
                    None
                )
                .is_some()
            );
        }
        output.finish_node();
        let (green, records) = (output.finish(), recover.finish_recoveries_for_test());
        assert_eq!(green.to_string(), source);
        assert_eq!(input, "");
        assert_eq!(records, [record(0, role, at..at, None)]);
    }
}

#[test]
fn fenced_literal_slots_keep_the_pending_fence_and_exact_coordinates() {
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
    for (body, roles) in [
        ("~\"α\r\n", vec![LiteralRole::RuleLiteralTerminator]),
        (
            "~\"{a\r\n",
            vec![
                LiteralRole::RuleLiteralInterpolationCloseBrace,
                LiteralRole::RuleLiteralTerminator,
            ],
        ),
        (
            "~\":{α\r\n",
            vec![
                LiteralRole::RuleLazyCaptureCloseBrace,
                LiteralRole::RuleLiteralTerminator,
            ],
        ),
    ] {
        let source = format!("{body}> ```\nouter");
        let operators = OperatorTable::empty();
        let mut recover = Recover::new_for_test(&operators);
        let mut input = source.as_str();
        let opener = scan_expression_rule_literal_opener_witness(chasa_recover::In::new(
            &mut input,
            &mut crate::cursor::LexRecover::new_for_test(recover.operators()),
            (),
        ))
        .unwrap();
        let mut output = GreenNodeBuilder::new();
        output.start_node(SyntaxKind::Root.into());
        rule_literal_normalized(
            crate::cursor::SyntaxIn::new(&mut input, &mut recover, &mut output),
            opener,
            202,
            LineEntry::InLine,
            Some(&fence),
            Some(AmbientClaimView::root_statement(0)).into(),
        );
        output.finish_node();
        let (_, records) = (output.finish(), recover.finish_recoveries_for_test());
        let at = 200 + body.len();
        let expected: Vec<_> = roles
            .into_iter()
            .enumerate()
            .map(|(id, role)| record(id as u32, role, at..at, None))
            .collect();
        assert_eq!(records, expected, "{source:?}");
        assert_eq!(input, "> ```\nouter");
    }
}

#[test]
fn rejected_rule_literal_opener_is_effect_free() {
    let operators = OperatorTable::empty();
    let recover = Recover::new_for_test(&operators);
    let mut input = "~ name";
    assert!(
        scan_expression_rule_literal_opener_witness(chasa_recover::In::new(
            &mut input,
            &mut crate::cursor::LexRecover::new_for_test(recover.operators()),
            ()
        ))
        .is_none()
    );
    assert_eq!(input, "~ name");
}

#[test]
fn one_item_error_range_includes_crlf_and_foreign_prefix() {
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
    let source = "~\"{\r\n> ;}\"";
    let operators = OperatorTable::empty();
    let mut recover = Recover::new_for_test(&operators);
    let mut input = source;
    let opener = scan_expression_rule_literal_opener_witness(chasa_recover::In::new(
        &mut input,
        &mut crate::cursor::LexRecover::new_for_test(recover.operators()),
        (),
    ))
    .unwrap();
    let mut output = GreenNodeBuilder::new();
    output.start_node(SyntaxKind::Root.into());
    rule_literal_normalized(
        crate::cursor::SyntaxIn::new(&mut input, &mut recover, &mut output),
        opener,
        102,
        LineEntry::InLine,
        Some(&fence),
        Some(AmbientClaimView::root_statement(0)).into(),
    );
    output.finish_node();
    let (green, records) = (output.finish(), recover.finish_recoveries_for_test());
    assert_eq!(green.to_string(), source);
    assert_eq!(input, "");
    assert_eq!(
        records,
        [record(
            0,
            LiteralRole::RuleUnexpectedItem,
            103..108,
            Some(UnexpectedCategory::Punctuation(
                PunctuationEvidence::Semicolon
            ))
        )]
    );
}
