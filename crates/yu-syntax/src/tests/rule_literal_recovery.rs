use crate::tests::support::*;
use crate::{
    SourceText, SyntaxEnvironment,
    ambient_claim::AmbientClaimView,
    literal::{rule_literal_normalized, scan_expression_rule_literal_opener_witness},
    parse_file,
    recovery_record::{
        Delimiter, DiagnosticId, ExpectationSources, ExpectedSyntax, GrammarRole, LiteralExpected,
        LiteralRole, PunctuationEvidence, RecoveryKind, RecoverySiteKey, SyntaxExpectation,
        UnexpectedCategory, UnexpectedSyntax,
    },
    rule::{rule_body_witness, scan_rule_current_item_witness, scan_rule_item_witness},
    scan_header,
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

fn range(node: &SyntaxNode) -> Range<usize> {
    let range = node.text_range();
    usize::from(range.start())..usize::from(range.end())
}

fn child_kinds(node: &SyntaxNode) -> Vec<SyntaxKind> {
    node.children_with_tokens()
        .map(|child| child.kind())
        .collect()
}

#[test]
fn dedicated_rule_slots_are_directly_readable_from_the_rowan_tree() {
    // The body and a parenthesized item each own a distinct close slot.  The
    // equal insertion coordinate is deliberately insufficient without the
    // parent path.
    let source = "{(a";
    let (green, records) = parse(source, 0, None);
    let root = SyntaxNode::new_root(green);
    assert_eq!(root.kind(), SyntaxKind::Root);
    assert_eq!(root.to_string(), source);
    assert_eq!(child_kinds(&root), [SyntaxKind::RuleBody]);
    let body = root.children().next().expect("RuleBody");
    assert_eq!(body.kind(), SyntaxKind::RuleBody);
    assert_eq!(body.parent(), Some(root.clone()));
    assert_eq!(
        child_kinds(&body),
        [
            SyntaxKind::LBrace,
            SyntaxKind::RuleAlternation,
            SyntaxKind::Missing
        ]
    );
    let mut parent = body.clone();
    for (kind, children) in [
        (SyntaxKind::RuleAlternation, vec![SyntaxKind::RuleSequence]),
        (SyntaxKind::RuleSequence, vec![SyntaxKind::RuleItem]),
    ] {
        let child = parent.children().next().expect("direct Rule child");
        assert_eq!(child.kind(), kind);
        assert_eq!(child.parent(), Some(parent));
        assert_eq!(child_kinds(&child), children);
        parent = child;
    }
    let item = parent.children().next().expect("parenthesized RuleItem");
    assert_eq!(item.kind(), SyntaxKind::RuleItem);
    assert_eq!(item.parent(), Some(parent));
    assert_eq!(
        child_kinds(&item),
        [
            SyntaxKind::LParen,
            SyntaxKind::RuleAlternation,
            SyntaxKind::Missing
        ]
    );
    let mut parent = item.clone();
    for (kind, children) in [
        (SyntaxKind::RuleAlternation, vec![SyntaxKind::RuleSequence]),
        (SyntaxKind::RuleSequence, vec![SyntaxKind::RuleItem]),
        (SyntaxKind::RuleItem, vec![SyntaxKind::Identifier]),
    ] {
        let child = parent.children().next().expect("direct nested Rule child");
        assert_eq!(child.kind(), kind);
        assert_eq!(child.parent(), Some(parent));
        assert_eq!(child_kinds(&child), children);
        parent = child;
    }
    for (owner, kind, text, token_range) in [
        (&body, SyntaxKind::LBrace, "{", 0..1),
        (&item, SyntaxKind::LParen, "(", 1..2),
        (&parent, SyntaxKind::Identifier, "a", 2..3),
    ] {
        let token = owner
            .first_child_or_token()
            .and_then(|child| child.into_token())
            .expect("direct native token");
        assert_eq!(token.kind(), kind);
        assert_eq!(token.text(), text);
        assert_eq!(
            usize::from(token.text_range().start())..usize::from(token.text_range().end()),
            token_range
        );
        assert_eq!(token.parent(), Some(owner.clone()));
    }
    // Natural descendant preorder visits the inner close before the outer close.
    let missing = root
        .descendants()
        .filter(|node| node.kind() == SyntaxKind::Missing)
        .collect::<Vec<_>>();
    assert_eq!(missing.len(), 2);
    assert_eq!(missing[0].parent(), Some(item.clone()));
    assert_eq!(missing[1].parent(), Some(body.clone()));
    let mut derived = Vec::new();
    for node in &missing {
        assert_eq!(range(node), 3..3);
        assert_eq!(node.children_with_tokens().count(), 0);
        assert_eq!(node.to_string(), "");
        let owner = node.parent().expect("direct close owner");
        assert_eq!(owner.last_child_or_token(), Some(node.clone().into()));
        let opener = owner
            .first_child_or_token()
            .and_then(|child| child.into_token())
            .expect("direct close-owner opener");
        let (role, delimiter) = match (owner.kind(), opener.kind()) {
            (SyntaxKind::RuleItem, SyntaxKind::LParen) => {
                (LiteralRole::RuleParenClose, Delimiter::Parenthesis)
            }
            (SyntaxKind::RuleBody, SyntaxKind::LBrace) => {
                (LiteralRole::RuleBodyCloseBrace, Delimiter::Brace)
            }
            other => panic!("unexpected close-slot owner/opener: {other:?}"),
        };
        derived.push((role, delimiter, range(node)));
    }
    assert_eq!(
        derived,
        [
            (LiteralRole::RuleParenClose, Delimiter::Parenthesis, 3..3),
            (LiteralRole::RuleBodyCloseBrace, Delimiter::Brace, 3..3),
        ]
    );
    let expected_records = derived
        .into_iter()
        .enumerate()
        .map(|(id, (role, delimiter, range))| {
            let expected = record(id as u32, role, range, None);
            assert_eq!(expected.expectations.len(), 1);
            assert_eq!(
                expected.expectations[0].expected,
                ExpectedSyntax::Punctuation(PunctuationEvidence::Close(delimiter))
            );
            assert_eq!(expected.primary_expectation, 0);
            expected
        })
        .collect::<Vec<_>>();
    assert_eq!(records, expected_records);

    // A capture is terminal in its outer item.  The Error is direct capture
    // content; the following Missing or admitted RuleItem selects the RHS.
    for (source, expected, rhs, close_range) in [
        (
            "{a=;}",
            vec![SyntaxKind::Equals, SyntaxKind::Error, SyntaxKind::Missing],
            None,
            4..5,
        ),
        (
            "{a=; b?}",
            vec![SyntaxKind::Equals, SyntaxKind::Error, SyntaxKind::RuleItem],
            Some(" b?"),
            7..8,
        ),
    ] {
        let (green, _) = parse(source, 0, None);
        let root = SyntaxNode::new_root(green);
        assert_eq!(root.to_string(), source);
        let body = root.children().next().expect("RuleBody");
        assert_eq!(body.kind(), SyntaxKind::RuleBody);
        assert_eq!(body.parent(), Some(root.clone()));
        let close = body
            .last_child_or_token()
            .and_then(|child| child.into_token())
            .expect("final native RuleBody RBrace");
        assert_eq!(close.kind(), SyntaxKind::RBrace);
        assert_eq!(close.text(), "}");
        assert_eq!(
            usize::from(close.text_range().start())..usize::from(close.text_range().end()),
            close_range
        );
        assert_eq!(close.parent(), Some(body));
        assert_eq!(root.last_token(), Some(close));
        let capture = root
            .descendants()
            .find(|node| node.kind() == SyntaxKind::RuleCapture)
            .expect("RuleCapture");
        assert_eq!(child_kinds(&capture), expected, "{source:?}");
        let equals = capture
            .children_with_tokens()
            .next()
            .and_then(|child| child.into_token())
            .expect("capture Equals");
        assert_eq!(equals.kind(), SyntaxKind::Equals);
        assert_eq!(equals.text(), "=");
        let error = capture
            .children_with_tokens()
            .find_map(|child| {
                child
                    .into_token()
                    .filter(|token| token.kind() == SyntaxKind::Error)
            })
            .expect("capture Error leaf");
        assert_eq!(error.text(), ";");
        assert_eq!(
            usize::from(error.text_range().start())..usize::from(error.text_range().end()),
            3..4
        );
        assert_eq!(error.parent(), Some(capture.clone()));
        match rhs {
            None => {
                let missing = capture.children().last().expect("terminal RHS Missing");
                assert_eq!(missing.kind(), SyntaxKind::Missing);
                assert_eq!(range(&missing), 4..4);
                assert_eq!(missing.parent(), Some(capture.clone()));
                assert_eq!(missing.children_with_tokens().count(), 0);
                assert_eq!(missing.to_string(), "");
                assert_eq!(capture.to_string(), "=;");
            }
            Some(rhs) => {
                let rhs_item = capture.children().last().expect("admitted RHS RuleItem");
                assert_eq!(rhs_item.kind(), SyntaxKind::RuleItem);
                assert_eq!(rhs_item.to_string(), rhs);
                assert_eq!(
                    child_kinds(&rhs_item),
                    [
                        SyntaxKind::Whitespace,
                        SyntaxKind::Identifier,
                        SyntaxKind::RuleQuantifier
                    ]
                );
                assert_eq!(range(&rhs_item), 4..7);
                assert_eq!(rhs_item.parent(), Some(capture.clone()));
                let mut elements = rhs_item.children_with_tokens();
                for (kind, text, expected_range) in [
                    (SyntaxKind::Whitespace, " ", 4..5),
                    (SyntaxKind::Identifier, "b", 5..6),
                ] {
                    let token = elements
                        .next()
                        .and_then(|child| child.into_token())
                        .expect("direct RHS token");
                    assert_eq!(token.kind(), kind);
                    assert_eq!(token.text(), text);
                    assert_eq!(
                        usize::from(token.text_range().start())
                            ..usize::from(token.text_range().end()),
                        expected_range
                    );
                    assert_eq!(token.parent(), Some(rhs_item.clone()));
                }
                let quantifier = elements
                    .next()
                    .and_then(|child| child.into_node())
                    .expect("direct RHS RuleQuantifier");
                assert!(elements.next().is_none());
                assert_eq!(quantifier.kind(), SyntaxKind::RuleQuantifier);
                assert_eq!(range(&quantifier), 6..7);
                assert_eq!(quantifier.parent(), Some(rhs_item.clone()));
                assert_eq!(child_kinds(&quantifier), [SyntaxKind::RuleQuantifierToken]);
                let punctuation = quantifier
                    .first_child_or_token()
                    .and_then(|child| child.into_token())
                    .expect("quantifier punctuation token");
                assert_eq!(punctuation.kind(), SyntaxKind::RuleQuantifierToken);
                assert_eq!(punctuation.text(), "?");
                assert_eq!(
                    usize::from(punctuation.text_range().start())
                        ..usize::from(punctuation.text_range().end()),
                    6..7
                );
                assert_eq!(punctuation.parent(), Some(quantifier));
                assert!(
                    capture
                        .descendants()
                        .all(|node| node.kind() != SyntaxKind::Missing)
                );
            }
        }
        let outer = capture.parent().expect("capturing RuleItem");
        assert_eq!(outer.kind(), SyntaxKind::RuleItem);
        assert_eq!(
            child_kinds(&outer),
            [SyntaxKind::Identifier, SyntaxKind::RuleCapture],
            "capture owns the terminal RHS rather than leaving an outer postfix"
        );
        assert_eq!(
            outer
                .children()
                .filter(|node| node.kind() == SyntaxKind::RuleItem)
                .count(),
            0
        );
    }

    // A protected body close leaves the required name Missing in its direct
    // postfix owner, while the body consumes the native close unchanged.
    for (source, tail, introducer_kind, introducer_text, close_start, role) in [
        (
            "{a.}",
            SyntaxKind::RuleField,
            SyntaxKind::Dot,
            ".",
            3,
            LiteralRole::RuleFieldName,
        ),
        (
            "{a::}",
            SyntaxKind::RulePath,
            SyntaxKind::ColonColon,
            "::",
            4,
            LiteralRole::RulePathName,
        ),
    ] {
        let (green, records) = parse(source, 0, None);
        let root = SyntaxNode::new_root(green);
        assert_eq!(root.kind(), SyntaxKind::Root);
        assert_eq!(root.parent(), None);
        assert_eq!(root.to_string(), source);
        assert_eq!(range(&root), 0..close_start + 1);
        assert_eq!(child_kinds(&root), [SyntaxKind::RuleBody]);
        let body = root.first_child().expect("direct RuleBody");
        assert_eq!(body.kind(), SyntaxKind::RuleBody);
        assert_eq!(body.parent(), Some(root.clone()));
        assert_eq!(range(&body), 0..close_start + 1);
        assert_eq!(
            child_kinds(&body),
            [
                SyntaxKind::LBrace,
                SyntaxKind::RuleAlternation,
                SyntaxKind::RBrace
            ]
        );
        let mut parent = body.clone();
        for (kind, children) in [
            (SyntaxKind::RuleAlternation, vec![SyntaxKind::RuleSequence]),
            (SyntaxKind::RuleSequence, vec![SyntaxKind::RuleItem]),
            (SyntaxKind::RuleItem, vec![SyntaxKind::Identifier, tail]),
        ] {
            let child = parent.first_child().expect("direct Rule child");
            assert_eq!(child.kind(), kind);
            assert_eq!(child.parent(), Some(parent));
            assert_eq!(range(&child), 1..close_start);
            assert_eq!(child_kinds(&child), children);
            parent = child;
        }
        let item = parent;
        let owner = item.first_child().expect("direct required-name owner");
        assert_eq!(owner.kind(), tail);
        assert_eq!(owner.parent(), Some(item.clone()));
        assert_eq!(range(&owner), 2..close_start);
        assert_eq!(child_kinds(&owner), [introducer_kind, SyntaxKind::Missing]);
        for (token_owner, kind, text, token_range) in [
            (&body, SyntaxKind::LBrace, "{", 0..1),
            (&item, SyntaxKind::Identifier, "a", 1..2),
            (&owner, introducer_kind, introducer_text, 2..close_start),
        ] {
            let token = token_owner
                .first_child_or_token()
                .and_then(|child| child.into_token())
                .expect("direct native token");
            assert_eq!(token.kind(), kind);
            assert_eq!(token.text(), text);
            assert_eq!(token.parent(), Some(token_owner.clone()));
            assert_eq!(
                usize::from(token.text_range().start())..usize::from(token.text_range().end()),
                token_range
            );
        }
        let missing = owner.first_child().expect("direct name Missing");
        assert_eq!(missing.kind(), SyntaxKind::Missing);
        assert_eq!(missing.parent(), Some(owner.clone()));
        assert_eq!(range(&missing), close_start..close_start);
        assert_eq!(missing.children_with_tokens().count(), 0);
        assert_eq!(missing.to_string(), "");
        assert_eq!(owner.last_child_or_token(), Some(missing.clone().into()));
        assert_eq!(
            root.descendants()
                .filter(|node| node.kind() == SyntaxKind::Missing)
                .collect::<Vec<_>>(),
            [missing.clone()]
        );
        assert!(
            root.descendants_with_tokens()
                .all(|element| !matches!(element.kind(), SyntaxKind::Error | SyntaxKind::Invalid))
        );
        let close = body
            .last_child_or_token()
            .and_then(|child| child.into_token())
            .expect("final native RuleBody RBrace");
        assert_eq!(close.kind(), SyntaxKind::RBrace);
        assert_eq!(close.text(), "}");
        assert_eq!(close.parent(), Some(body));
        assert_eq!(
            usize::from(close.text_range().start())..usize::from(close.text_range().end()),
            close_start..close_start + 1
        );
        assert_eq!(root.last_token(), Some(close));

        let missing_owner = missing.parent().expect("required-name owner");
        let introducer = missing_owner
            .first_child_or_token()
            .and_then(|child| child.into_token())
            .expect("required-name introducer");
        let derived_role = match (missing_owner.kind(), introducer.kind()) {
            (SyntaxKind::RuleField, SyntaxKind::Dot) => LiteralRole::RuleFieldName,
            (SyntaxKind::RulePath, SyntaxKind::ColonColon) => LiteralRole::RulePathName,
            other => panic!("unexpected required-name owner/introducer: {other:?}"),
        };
        let derived = (
            GrammarRole::Literal(derived_role),
            range(&missing),
            [ExpectedSyntax::Identifier],
            0,
        );
        assert_eq!(
            derived,
            (
                GrammarRole::Literal(role),
                close_start..close_start,
                [ExpectedSyntax::Identifier],
                0,
            )
        );
        let expected = record(0, derived_role, derived.1, None);
        assert_eq!(expected.expectations.len(), derived.2.len());
        assert_eq!(expected.expectations[0].expected, derived.2[0]);
        assert_eq!(expected.primary_expectation, derived.3);
        assert_eq!(records, [expected]);
    }

    // Name failure consumes exactly one lexical item.  The subsequent item is
    // owned by the outer sequence, rather than retried inside RuleField/Path.
    for (source, tail, opener_kind, opener_text, error_text, expected_range) in [
        (
            "{a.12 b}",
            SyntaxKind::RuleField,
            SyntaxKind::Dot,
            ".",
            "12",
            3..5,
        ),
        (
            "{a::💥 b}",
            SyntaxKind::RulePath,
            SyntaxKind::ColonColon,
            "::",
            "💥",
            4..8,
        ),
    ] {
        let (green, _) = parse(source, 0, None);
        let root = SyntaxNode::new_root(green);
        assert_eq!(root.kind(), SyntaxKind::Root);
        assert_eq!(root.to_string(), source);
        assert_eq!(child_kinds(&root), [SyntaxKind::RuleBody]);
        let body = root.first_child().expect("direct RuleBody");
        assert_eq!(body.parent(), Some(root.clone()));
        assert_eq!(
            child_kinds(&body),
            [
                SyntaxKind::LBrace,
                SyntaxKind::RuleAlternation,
                SyntaxKind::RBrace
            ]
        );
        let alternation = body.first_child().expect("direct RuleAlternation");
        assert_eq!(alternation.kind(), SyntaxKind::RuleAlternation);
        assert_eq!(alternation.parent(), Some(body.clone()));
        assert_eq!(child_kinds(&alternation), [SyntaxKind::RuleSequence]);
        let sequence = alternation.first_child().expect("direct RuleSequence");
        assert_eq!(sequence.kind(), SyntaxKind::RuleSequence);
        assert_eq!(sequence.parent(), Some(alternation));
        assert_eq!(
            child_kinds(&sequence),
            [SyntaxKind::RuleItem, SyntaxKind::RuleItem]
        );
        let items = sequence.children().collect::<Vec<_>>();
        assert_eq!(items.len(), 2, "{source:?}");
        assert_eq!(items[0].parent(), Some(sequence.clone()));
        assert_eq!(range(&items[0]), 1..expected_range.end);
        assert_eq!(child_kinds(&items[0]), [SyntaxKind::Identifier, tail]);
        let failed = items[0].first_child().expect("direct failed name tail");
        assert_eq!(failed.kind(), tail);
        assert_eq!(failed.parent(), Some(items[0].clone()));
        assert_eq!(range(&failed), 2..expected_range.end);
        assert_eq!(
            child_kinds(&failed),
            [opener_kind, SyntaxKind::Error],
            "{source:?}"
        );
        let opener_token = failed
            .children_with_tokens()
            .next()
            .and_then(|child| child.into_token())
            .expect("tail opener");
        assert_eq!(opener_token.kind(), opener_kind);
        assert_eq!(opener_token.text(), opener_text);
        assert_eq!(opener_token.parent(), Some(failed.clone()));
        assert_eq!(
            usize::from(opener_token.text_range().start())
                ..usize::from(opener_token.text_range().end()),
            2..expected_range.start
        );
        let error = failed
            .children_with_tokens()
            .nth(1)
            .and_then(|child| child.into_token())
            .expect("name Error leaf");
        assert_eq!(error.kind(), SyntaxKind::Error);
        assert_eq!(error.text(), error_text);
        assert_eq!(error.parent(), Some(failed));
        assert_eq!(
            usize::from(error.text_range().start())..usize::from(error.text_range().end()),
            expected_range
        );
        assert_eq!(items[1].parent(), Some(sequence));
        assert_eq!(range(&items[1]), expected_range.end..source.len() - 1);
        assert_eq!(items[1].to_string(), " b", "{source:?}");
        assert_eq!(
            child_kinds(&items[1]),
            [SyntaxKind::Whitespace, SyntaxKind::Identifier]
        );
        let mut continuation = items[1].children_with_tokens();
        for (kind, text, token_range) in [
            (
                SyntaxKind::Whitespace,
                " ",
                expected_range.end..expected_range.end + 1,
            ),
            (
                SyntaxKind::Identifier,
                "b",
                expected_range.end + 1..expected_range.end + 2,
            ),
        ] {
            let token = continuation
                .next()
                .and_then(|child| child.into_token())
                .expect("direct continuation token");
            assert_eq!(token.kind(), kind);
            assert_eq!(token.text(), text);
            assert_eq!(token.parent(), Some(items[1].clone()));
            assert_eq!(
                usize::from(token.text_range().start())..usize::from(token.text_range().end()),
                token_range
            );
        }
        assert!(continuation.next().is_none());
        let close = body
            .last_child_or_token()
            .and_then(|child| child.into_token())
            .expect("direct native body close");
        assert_eq!(close.kind(), SyntaxKind::RBrace);
        assert_eq!(close.text(), "}");
        assert_eq!(close.parent(), Some(body));
        assert_eq!(
            usize::from(close.text_range().start())..usize::from(close.text_range().end()),
            source.len() - 1..source.len()
        );
    }

    // A non-capture postfix remains a sibling of the failed name owner.
    let (green, _) = parse("{a.12?}", 0, None);
    let root = SyntaxNode::new_root(green);
    let item = root
        .descendants()
        .find(|node| node.kind() == SyntaxKind::RuleItem && node.to_string() == "a.12?")
        .expect("outer RuleItem");
    assert_eq!(
        child_kinds(&item),
        [
            SyntaxKind::Identifier,
            SyntaxKind::RuleField,
            SyntaxKind::RuleQuantifier
        ]
    );
    let field = item.children().next().expect("failed RuleField");
    assert_eq!(child_kinds(&field), [SyntaxKind::Dot, SyntaxKind::Error]);
    let quantifier = item.children().nth(1).expect("outer RuleQuantifier");
    assert_eq!(quantifier.to_string(), "?");
    assert_eq!(quantifier.parent(), Some(item));

    // Consecutive raw leaves are one same-parent RuleSequence occurrence, not
    // a synthetic wrapper or one occurrence per token.
    let source = "{;💥}";
    let (green, _) = parse(source, 0, None);
    let root = SyntaxNode::new_root(green);
    assert_eq!(root.kind(), SyntaxKind::Root);
    assert_eq!(root.parent(), None);
    assert_eq!(root.to_string(), source);
    assert_eq!(range(&root), 0..7);
    assert_eq!(child_kinds(&root), [SyntaxKind::RuleBody]);
    let body = root.first_child().expect("direct RuleBody");
    assert_eq!(body.kind(), SyntaxKind::RuleBody);
    assert_eq!(body.parent(), Some(root.clone()));
    assert_eq!(range(&body), 0..7);
    assert_eq!(
        child_kinds(&body),
        [
            SyntaxKind::LBrace,
            SyntaxKind::RuleAlternation,
            SyntaxKind::RBrace
        ]
    );
    let alternation = body.first_child().expect("direct RuleAlternation");
    assert_eq!(alternation.kind(), SyntaxKind::RuleAlternation);
    assert_eq!(alternation.parent(), Some(body.clone()));
    assert_eq!(range(&alternation), 1..6);
    assert_eq!(child_kinds(&alternation), [SyntaxKind::RuleSequence]);
    let sequence = alternation.first_child().expect("direct RuleSequence");
    assert_eq!(sequence.kind(), SyntaxKind::RuleSequence);
    assert_eq!(sequence.parent(), Some(alternation.clone()));
    assert_eq!(range(&sequence), 1..6);
    assert_eq!(
        child_kinds(&sequence),
        [SyntaxKind::Error, SyntaxKind::Error]
    );
    for (child, kind, text, token_range) in [
        (body.first_child_or_token(), SyntaxKind::LBrace, "{", 0..1),
        (body.last_child_or_token(), SyntaxKind::RBrace, "}", 6..7),
    ] {
        let token = child
            .and_then(|child| child.into_token())
            .expect("direct native body delimiter");
        assert_eq!(token.kind(), kind);
        assert_eq!(token.text(), text);
        assert_eq!(token.parent(), Some(body.clone()));
        assert_eq!(
            usize::from(token.text_range().start())..usize::from(token.text_range().end()),
            token_range
        );
    }
    assert!(
        !root
            .descendants_with_tokens()
            .any(|child| matches!(child.kind(), SyntaxKind::Missing | SyntaxKind::Invalid))
    );
    let groups = crate::tests::recovery_output::recovery_groups(&root);
    assert_eq!(groups.len(), 1);
    let group = &groups[0];
    let crate::tests::recovery_output::RecoveryGroup::Raw(tokens) = group else {
        panic!("RuleSequence recovery must be raw Error leaves");
    };
    assert_eq!(
        tokens
            .iter()
            .map(|token| (token.kind(), token.text()))
            .collect::<Vec<_>>(),
        [(SyntaxKind::Error, ";"), (SyntaxKind::Error, "💥")]
    );
    assert_eq!(
        tokens[0].next_sibling_or_token(),
        Some(tokens[1].clone().into())
    );
    assert_eq!(group.text(), ";💥");
    assert_eq!(
        usize::from(group.text_range().start())..usize::from(group.text_range().end()),
        1..6
    );
    assert_eq!(group.parent(), Some(sequence.clone()));
    for (token, token_range) in tokens.iter().zip([1..2, 2..6]) {
        assert_eq!(token.parent(), Some(sequence.clone()));
        assert_eq!(
            usize::from(token.text_range().start())..usize::from(token.text_range().end()),
            token_range
        );
    }
    assert_eq!(
        sequence.first_child_or_token(),
        Some(tokens[0].clone().into())
    );
    assert_eq!(
        sequence.last_child_or_token(),
        Some(tokens[1].clone().into())
    );
    assert!(tokens[0].prev_sibling_or_token().is_none());
    assert!(tokens[1].next_sibling_or_token().is_none());

    // Select the repeated-Item expectation from the verified Body frame and
    // direct sequence slot, independently of Error spelling or parser records.
    let derived = groups
        .iter()
        .map(|group| {
            let owner = group.parent().expect("direct Error-group owner");
            let parent = owner.parent().expect("direct alternation");
            let frame = parent.parent().expect("direct Rule frame");
            let expected = match (frame.kind(), parent.kind(), owner.kind()) {
                (SyntaxKind::RuleBody, SyntaxKind::RuleAlternation, SyntaxKind::RuleSequence) => {
                    assert_eq!(frame, body);
                    assert_eq!(parent, alternation);
                    assert_eq!(owner, sequence);
                    ExpectedSyntax::Literal(LiteralExpected::RuleItem)
                }
                other => panic!("unexpected repeated-Item context: {other:?}"),
            };
            (
                expected,
                0usize,
                usize::from(group.text_range().start())..usize::from(group.text_range().end()),
            )
        })
        .collect::<Vec<_>>();
    assert_eq!(
        derived,
        [(ExpectedSyntax::Literal(LiteralExpected::RuleItem), 0, 1..6)]
    );

    // A physical line boundary belongs to RuleAlternation, after the failed
    // slot; it is not swallowed by name/RHS recovery.
    for (source, tail) in [
        ("{a.\nnext}", SyntaxKind::RuleField),
        ("{a=\r\nnext}", SyntaxKind::RuleCapture),
    ] {
        let (green, _) = parse(source, 0, None);
        let root = SyntaxNode::new_root(green);
        let alternation = root
            .descendants()
            .find(|node| node.kind() == SyntaxKind::RuleAlternation)
            .expect("outer RuleAlternation");
        assert_eq!(
            child_kinds(&alternation),
            [
                SyntaxKind::RuleSequence,
                SyntaxKind::Newline,
                SyntaxKind::RuleSequence
            ]
        );
        let failed = alternation
            .descendants()
            .find(|node| node.kind() == tail)
            .expect("failed dedicated slot");
        let missing = failed.children().last().expect("slot Missing");
        assert_eq!(missing.kind(), SyntaxKind::Missing);
        assert_eq!(range(&missing), 3..3);
        assert_eq!(missing.parent(), Some(failed));
        assert!(alternation.to_string().ends_with("next"), "{source:?}");
    }
}

#[test]
fn public_root_preserves_rule_eof_leading_outside_the_terminal_slots() {
    for (source, trailing) in [
        ("~\"{a=  ", vec![(SyntaxKind::Whitespace, "  ")]),
        ("~\"{a=\r\n", vec![(SyntaxKind::Newline, "\r\n")]),
        (
            "~\"{a= // trailing",
            vec![
                (SyntaxKind::Whitespace, " "),
                (SyntaxKind::LineComment, "// trailing"),
            ],
        ),
    ] {
        let source: Arc<SourceText> = Arc::from(source);
        let header = Arc::new(scan_header(Arc::clone(&source)));
        let parsed = parse_file(
            Arc::clone(&source),
            header,
            Arc::new(SyntaxEnvironment::empty()),
        );
        assert_eq!(parsed.green().to_string(), source.as_ref());
        let root = SyntaxNode::new_root(parsed.green().clone());
        let literal = root
            .descendants()
            .find(|node| node.kind() == SyntaxKind::RuleLiteral)
            .expect("RuleLiteral");
        let capture = literal
            .descendants()
            .find(|node| node.kind() == SyntaxKind::RuleCapture)
            .expect("terminal RuleCapture");
        assert_eq!(
            child_kinds(&capture),
            [SyntaxKind::Equals, SyntaxKind::Missing]
        );
        let missing = capture.children().last().expect("capture RHS Missing");
        assert_eq!(range(&missing), 5..5);
        assert_eq!(missing.parent(), Some(capture));

        let root_elements = root.children_with_tokens().collect::<Vec<_>>();
        let trailing_tokens = root_elements
            .iter()
            .skip_while(|element| element.as_node().is_some())
            .map(|element| {
                let token = element.as_token().expect("native Root leading token");
                (token.kind(), token.text().to_owned())
            })
            .collect::<Vec<_>>();
        assert_eq!(
            trailing_tokens,
            trailing
                .into_iter()
                .map(|(kind, text)| (kind, text.to_owned()))
                .collect::<Vec<_>>(),
            "{source:?}"
        );
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
