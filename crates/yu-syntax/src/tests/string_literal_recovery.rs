use crate::tests::support::*;
use crate::{
    ambient_claim::AmbientClaimView,
    handoff::MlMode,
    lexical::yumark::{FenceOpener, FencePrefixPolicy},
    literal::{
        StringLiteralExit, scan_string_opener_witness,
        string_literal_with_virtual_statements_normalized, string_literal_witness,
    },
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
    let mut recover = Recover::new_for_test(&operators);
    let mut input = source;
    let (opener, mode) = scan_string_opener_witness(chasa_recover::In::new(
        &mut input,
        &mut crate::cursor::LexRecover::new_for_test(recover.operators()),
        (),
    ))
    .unwrap();
    let mut output = frozen
        .map(|records| {
            recover = Recover::reconcile_for_test(recover.operators(), records);
            GreenNodeBuilder::new()
        })
        .unwrap_or_else(GreenNodeBuilder::new);
    output.start_node(SyntaxKind::Root.into());
    let part_origin = origin + source.len() - input.len();
    string_literal_with_virtual_statements_normalized(
        crate::cursor::SyntaxIn::new(&mut input, &mut recover, &mut output),
        opener,
        mode,
        part_origin,
        fence,
        Some(AmbientClaimView::root_statement(0)).into(),
    );
    output.finish_node();
    let (green, records) = (output.finish(), recover.finish_recoveries_for_test());
    (green, records, input)
}

fn range(node: &SyntaxNode) -> Range<usize> {
    usize::from(node.text_range().start())..usize::from(node.text_range().end())
}

fn string_literal(root: &SyntaxNode) -> SyntaxNode {
    root.descendants()
        .find(|node| node.kind() == SyntaxKind::StringLiteral)
        .expect("fixture admits a StringLiteral")
}

fn direct_kinds(node: &SyntaxNode) -> Vec<SyntaxKind> {
    node.children_with_tokens()
        .map(|element| element.kind())
        .collect()
}

fn final_missing(literal: &SyntaxNode) -> SyntaxNode {
    let missing = literal
        .children_with_tokens()
        .last()
        .and_then(|element| element.into_node())
        .expect("StringLiteral final child is a Missing node");
    assert_eq!(missing.kind(), SyntaxKind::Missing);
    missing
}

fn unreachable_interpolation_body(_: SyntaxIn) -> crate::lexical::item::Item {
    panic!("the string-terminator fixture has no interpolation")
}

fn parse_string_driver<'s>(
    source: &'s str,
    boundary: &FenceBoundary,
) -> (GreenNode, StringLiteralExit, &'s str) {
    let operators = OperatorTable::empty();
    let mut recover = Recover::new_for_test(&operators);
    let mut input = source;
    let (opener, mode) = scan_string_opener_witness(chasa_recover::In::new(
        &mut input,
        &mut crate::cursor::LexRecover::new_for_test(recover.operators()),
        (),
    ))
    .expect("string opener");
    let interior_origin = source.len() - input.len();
    let mut output = GreenNodeBuilder::new();
    output.start_node(SyntaxKind::Root.into());
    let exit = string_literal_witness(
        SyntaxIn::new(&mut input, &mut recover, &mut output),
        opener,
        mode,
        interior_origin,
        boundary,
        unreachable_interpolation_body,
    );
    output.finish_node();
    let (green, _) = (output.finish(), recover.finish_recoveries_for_test());
    (green, exit, input)
}

#[test]
fn string_terminator_slot_has_a_final_direct_rowan_child() {
    // These assertions intentionally read only the produced Rowan tree.  The
    // record tests below remain the compatibility control for the temporary
    // recovery ledger.
    for (source, expected_children, end_range) in [
        (
            "\"\"",
            vec![SyntaxKind::StringStart, SyntaxKind::StringEnd],
            1..2,
        ),
        (
            "\"α\"",
            vec![
                SyntaxKind::StringStart,
                SyntaxKind::StringText,
                SyntaxKind::StringEnd,
            ],
            3..4,
        ),
        (
            "\"\"\"α\"\"\"",
            vec![
                SyntaxKind::StringStart,
                SyntaxKind::StringText,
                SyntaxKind::StringEnd,
            ],
            5..8,
        ),
    ] {
        let (green, _, remainder) = parse(source, 0, None, None);
        assert_eq!(remainder, "");
        let root = SyntaxNode::new_root(green);
        let literal = string_literal(&root);
        assert_eq!(direct_kinds(&literal), expected_children, "{source:?}");
        let end = literal
            .children_with_tokens()
            .last()
            .expect("StringLiteral has a terminator");
        assert_eq!(end.kind(), SyntaxKind::StringEnd);
        assert_eq!(
            usize::from(end.text_range().start())..usize::from(end.text_range().end()),
            end_range,
        );
    }

    // A two-quote run cannot close a three-quote literal: it is text, then the
    // outer slot itself is the final zero-width Missing child.
    let source = "\"\"\"α\"\"";
    let (green, _, remainder) = parse(source, 0, None, None);
    assert_eq!(remainder, "");
    let root = SyntaxNode::new_root(green);
    let literal = string_literal(&root);
    assert_eq!(
        direct_kinds(&literal),
        [
            SyntaxKind::StringStart,
            SyntaxKind::StringText,
            SyntaxKind::Missing
        ]
    );
    let missing = final_missing(&literal);
    assert_eq!(missing.parent(), Some(literal.clone()));
    assert!(missing.text_range().is_empty());
    assert_eq!(range(&missing), source.len()..source.len());
}

#[test]
fn string_terminator_slot_retains_prefixes_child_failures_and_boundaries() {
    // A physical quote prefix belongs to the StringLiteral directly, before
    // the accepted final close; it is neither text search nor a recovery node.
    let source = "\"\n> x\"";
    let (green, exit, remainder) = parse_string_driver(source, &fence());
    assert_eq!(exit, StringLiteralExit::Complete);
    assert_eq!(remainder, "");
    let root = SyntaxNode::new_root(green);
    let literal = string_literal(&root);
    assert_eq!(
        direct_kinds(&literal),
        [
            SyntaxKind::StringStart,
            SyntaxKind::StringText,
            SyntaxKind::YmQuotePrefix,
            SyntaxKind::StringText,
            SyntaxKind::StringEnd,
        ]
    );
    assert_eq!(
        literal.children_with_tokens().last().unwrap().kind(),
        SyntaxKind::StringEnd
    );

    // Child recovery remains nested before the equal-offset outer terminator.
    let source = "\"\\u{";
    let (green, _, remainder) = parse(source, 0, None, None);
    assert_eq!(remainder, "");
    let root = SyntaxNode::new_root(green);
    let literal = string_literal(&root);
    let outer = final_missing(&literal);
    assert_eq!(range(&outer), source.len()..source.len());
    let escape = literal
        .children()
        .find(|node| node.kind() == SyntaxKind::StringEscape)
        .expect("unicode escape remains a StringLiteral child");
    let nested = escape
        .descendants()
        .filter(|node| node.kind() == SyntaxKind::Missing)
        .collect::<Vec<_>>();
    assert_eq!(nested.len(), 2);
    assert!(
        nested
            .iter()
            .all(|node| range(node) == (source.len()..source.len()))
    );
    let preorder = root
        .descendants()
        .filter(|node| node.kind() == SyntaxKind::Missing)
        .collect::<Vec<_>>();
    assert_eq!(preorder, [nested[0].clone(), nested[1].clone(), outer]);

    // Malformed Unicode is still owned by its escape; EOF only adds the final
    // StringLiteral child, at the root-relative end of the UTF-8 spelling.
    let source = "\"\\u{💥";
    let (green, _, remainder) = parse(source, 0, None, None);
    assert_eq!(remainder, "");
    let root = SyntaxNode::new_root(green);
    let literal = string_literal(&root);
    let outer = final_missing(&literal);
    assert_eq!(range(&outer), source.len()..source.len());
    let escape = literal
        .children()
        .find(|node| node.kind() == SyntaxKind::StringEscape)
        .unwrap();
    assert!(
        escape
            .descendants_with_tokens()
            .any(|element| element.kind() == SyntaxKind::Error)
    );

    // Format text treats quotes as raw content.  The quote after the completed
    // interpolation is the only StringLiteral terminator.
    let source = "\"%fmt\"\\}\r\n🌱{}後\"";
    let (green, _, remainder) = parse(source, 0, None, None);
    assert_eq!(remainder, "");
    let root = SyntaxNode::new_root(green);
    let literal = string_literal(&root);
    assert_eq!(
        literal.children_with_tokens().last().unwrap().kind(),
        SyntaxKind::StringEnd
    );
    assert!(
        literal
            .descendants_with_tokens()
            .any(|element| element.kind() == SyntaxKind::StringInterpolationFormatText)
    );

    // EOF after CRLF likewise leaves the final outer child at the exact
    // root-relative byte coordinate, including the two physical line bytes.
    let source = "\"α\r\n";
    let (green, _, remainder) = parse(source, 0, None, None);
    assert_eq!(remainder, "");
    let root = SyntaxNode::new_root(green);
    let literal = string_literal(&root);
    let missing = final_missing(&literal);
    assert_eq!(range(&missing), source.len()..source.len());
    assert_eq!(literal.to_string(), source);

    // The fence Item is not emitted: the zero-width final child is at the
    // consumed CRLF end and the exact fence suffix remains pending.
    let source = "\"α\r\n> ```\nouter";
    let (green, _, remainder) = parse(source, 0, Some(&fence()), None);
    assert_eq!(remainder, "> ```\nouter");
    let root = SyntaxNode::new_root(green);
    let literal = string_literal(&root);
    let missing = final_missing(&literal);
    assert_eq!(range(&missing), 5..5);
    assert_eq!(literal.to_string(), "\"α\r\n");
}

#[test]
fn expression_caller_keeps_the_string_terminator_as_its_final_literal_child() {
    let source = "\"α";
    let operators = OperatorTable::empty();
    let mut recover = Recover::new_for_test(&operators);
    let mut input = source;
    let mut output = GreenNodeBuilder::new();
    output.start_node(SyntaxKind::Root.into());
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
            None,
        )
        .is_some()
    );
    output.finish_node();
    let (green, records) = (output.finish(), recover.finish_recoveries_for_test());
    assert_eq!(input, "");
    // This remains a record control; the topology proof below does not derive
    // anything from it.
    assert_eq!(
        records,
        [record(
            0,
            LiteralRole::StringTerminator,
            RecoveryKind::Missing,
            3..3
        )]
    );
    let root = SyntaxNode::new_root(green);
    let literal = string_literal(&root);
    let missing = final_missing(&literal);
    assert_eq!(missing.parent(), Some(literal));
    assert_eq!(range(&missing), 3..3);
}

#[test]
fn pattern_and_rule_callers_keep_root_relative_final_string_terminators() {
    for (source, pattern, end_range) in [
        ("\"\"\"\\u{}\"\"\"", true, 7..10),
        ("~\"{a=\"\\u{}\"}\"", false, 10..11),
    ] {
        let operators = OperatorTable::empty();
        let mut recover = Recover::new_for_test(&operators);
        let mut input = source;
        let mut output = GreenNodeBuilder::new();
        output.start_node(SyntaxKind::Root.into());
        if pattern {
            pattern_normalized(
                SyntaxIn::new(&mut input, &mut recover, &mut output),
                0,
                LineEntry::InLine,
                None,
                0,
                Some(AmbientClaimView::root_statement(0)).into(),
            );
        } else {
            assert!(
                expr_normalized(
                    SyntaxIn::new(&mut input, &mut recover, &mut output),
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
                )
                .is_some()
            );
        }
        output.finish_node();
        let (green, _) = (output.finish(), recover.finish_recoveries_for_test());
        assert_eq!(input, "", "{source:?}");
        let root = SyntaxNode::new_root(green);
        let literal = string_literal(&root);
        let end = literal
            .children_with_tokens()
            .last()
            .expect("actual caller preserves StringLiteral terminator");
        assert_eq!(end.kind(), SyntaxKind::StringEnd, "{source:?}");
        assert_eq!(
            usize::from(end.text_range().start())..usize::from(end.text_range().end()),
            end_range,
            "{source:?}"
        );
    }
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
        let error = crate::tests::recovery_output::recovery_groups(&root)
            .into_iter()
            .next()
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
    let recover = Recover::new_for_test(&operators);
    let mut input = "α";
    let mut output = GreenNodeBuilder::new();
    output.start_node(SyntaxKind::Root.into());
    output.token(SyntaxKind::Identifier.into(), "seed");
    assert!(
        scan_string_opener_witness(chasa_recover::In::new(
            &mut input,
            &mut crate::cursor::LexRecover::new_for_test(recover.operators()),
            ()
        ))
        .is_none()
    );
    assert_eq!(input, "α");
    assert_eq!(recover.recovery_slot_count(), 0);
    output.finish_node();
    assert_eq!(
        (output.finish(), recover.finish_recoveries_for_test())
            .0
            .to_string(),
        "seed"
    );
}

#[test]
fn actual_expression_pattern_and_rule_strings_keep_virtual_child_before_literal_parents() {
    for (source, pattern, at) in [
        ("\"%{,", false, 3),
        ("\"\"\"%{,", true, 5),
        ("~\"{a=\"%{,", false, 8),
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
                    None,
                )
                .is_some()
            );
        }
        output.finish_node();
        let (green, records) = (output.finish(), recover.finish_recoveries_for_test());
        assert_eq!(green.to_string(), source);
        assert_eq!(input, "");
        // Any enclosing Rule recovery follows this complete Virtual/String cone.
        assert_eq!(
            &records[..3],
            &[
                super::virtual_statement_block::virtual_record(
                    0,
                    crate::recovery_record::StatementRole::Starter,
                    RecoveryKind::Missing,
                    at..at
                ),
                record(
                    1,
                    LiteralRole::StringInterpolationCloseBrace,
                    RecoveryKind::Missing,
                    at + 1..at + 1
                ),
                record(
                    2,
                    LiteralRole::StringTerminator,
                    RecoveryKind::Missing,
                    at + 1..at + 1
                ),
            ]
        );
        let root = SyntaxNode::new_root(green);
        let missing: Vec<_> = root
            .descendants()
            .filter(|node| node.kind() == SyntaxKind::Missing)
            .take(3)
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
    }
}

#[test]
fn literal_recovery_preserves_seeded_ids_and_allocates_after_frozen_records() {
    use crate::cursor::recovery::RecoveryDraft;
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
        let mut recover = Recover::new_for_test(&operators);
        let mut output = if reconcile {
            {
                recover = Recover::reconcile_for_test(recover.operators(), &frozen);
                GreenNodeBuilder::new()
            }
        } else {
            GreenNodeBuilder::new()
        };
        output.start_node(SyntaxKind::Root.into());
        output.token(SyntaxKind::Identifier.into(), "seed");
        output.start_node(SyntaxKind::Missing.into());
        output.finish_node();
        recover.commit_recovery_for_test(RecoveryDraft::new(
            seed.site.clone(),
            seed.kind,
            seed.unexpected.clone(),
            seed.expectations.clone(),
            0,
        ));
        for origin in [10, 20] {
            let mut input = "\"\\u{}\"";
            let (opener, mode) = scan_string_opener_witness(chasa_recover::In::new(
                &mut input,
                &mut crate::cursor::LexRecover::new_for_test(recover.operators()),
                (),
            ))
            .unwrap();
            string_literal_with_virtual_statements_normalized(
                crate::cursor::SyntaxIn::new(&mut input, &mut recover, &mut output),
                opener,
                mode,
                origin + 1,
                None,
                Some(AmbientClaimView::root_statement(0)).into(),
            );
            assert_eq!(input, "");
        }
        output.finish_node();
        let (green, records) = (output.finish(), recover.finish_recoveries_for_test());
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
    // The existing driver intentionally stops at the interpolation body's
    // trailing EOF-leading trivia.  The CST does not fabricate those spaces:
    // its outer terminator remains the final StringLiteral child at byte 3.
    let root = SyntaxNode::new_root(green.clone());
    let literal = string_literal(&root);
    assert_eq!(literal.to_string(), "\"%{");
    assert!(!literal.to_string().contains("  "));
    assert_eq!(&"\"%{  "[literal.to_string().len()..], "  ");
    let outer = final_missing(&literal);
    assert_eq!(range(&outer), 3..3);
    let interpolation = literal
        .children()
        .find(|node| node.kind() == SyntaxKind::StringInterpolation)
        .expect("interpolation remains the preceding StringLiteral child");
    let nested = interpolation
        .descendants()
        .find(|node| node.kind() == SyntaxKind::Missing)
        .expect("interpolation close Missing");
    assert_eq!(range(&nested), 3..3);
    let preorder = root
        .descendants()
        .filter(|node| node.kind() == SyntaxKind::Missing)
        .collect::<Vec<_>>();
    assert_eq!(preorder, [nested, outer]);
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
            super::virtual_statement_block::virtual_record(
                0,
                crate::recovery_record::StatementRole::Starter,
                RecoveryKind::Missing,
                3..3
            ),
            record(
                1,
                LiteralRole::StringInterpolationCloseBrace,
                RecoveryKind::Missing,
                4..4
            ),
            record(
                2,
                LiteralRole::StringTerminator,
                RecoveryKind::Missing,
                4..4
            )
        ]
    );
    let (again, frozen, _) = parse("\"%{,", 0, None, Some(&records));
    assert_eq!(again, green);
    assert_eq!(frozen, records);
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
