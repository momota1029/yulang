use crate::tests::type_expr::bracket_arrow_recovery::arrow;
use crate::tests::type_expr::*;

fn row_record(
    id: u32,
    role: GrammarRole,
    expected: ExpectedSyntax,
    range: Range<usize>,
    category: Option<UnexpectedCategory>,
) -> CommittedRecoveryRecord {
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

pub(super) fn close(
    id: u32,
    range: Range<usize>,
    actual: Option<Delimiter>,
) -> CommittedRecoveryRecord {
    row_record(
        id,
        GrammarRole::ClosingDelimiter {
            owner: ConstructRole::BracketRow,
            delimiter: Delimiter::Bracket,
        },
        ExpectedSyntax::Punctuation(PunctuationEvidence::Close(Delimiter::Bracket)),
        range,
        actual.map(|delimiter| {
            UnexpectedCategory::Punctuation(PunctuationEvidence::Close(delimiter))
        }),
    )
}

fn item(id: u32, range: Range<usize>, error: bool) -> CommittedRecoveryRecord {
    row_record(
        id,
        GrammarRole::Type(TypeRole::BracketRowItem),
        ExpectedSyntax::TypeExpression,
        range,
        error.then_some(UnexpectedCategory::OtherCharacter),
    )
}

#[test]
fn bracket_row_accepted_controls_keep_attachment_layout_and_full_typeapply() {
    for source in [
        "[] T",
        "[e, f; g\nh] T",
        "T [A B] -> U",
        "G T[F A]->U",
        "T [A\n  ] -> U",
        "T [A,\n] -> U",
        "[[e] T] U",
        "T -> [e] U",
    ] {
        let root = assert_complete_type_recovery(source, 0, &[]);
        assert!(
            !root.descendants_with_tokens().any(|node| matches!(
                node.kind(),
                SyntaxKind::Missing | SyntaxKind::Error | SyntaxKind::Invalid
            )),
            "{source:?}"
        );
        assert!(
            root.descendants()
                .any(|node| node.kind() == SyntaxKind::BracketRow)
        );
    }
}

#[test]
fn bracket_row_item_errors_keep_retry_trivia_outside_the_error() {
    for (source, range, text, first) in [
        ("T [:] -> U", 3..4, ":", SyntaxKind::Colon),
        ("T [@ A] -> U", 3..4, "@", SyntaxKind::Unknown),
        ("T [@ : A] -> U", 3..6, "@ :", SyntaxKind::Unknown),
        ("T [@\nA] -> U", 3..4, "@", SyntaxKind::Unknown),
        ("T [@\n  A] -> U", 3..4, "@", SyntaxKind::Unknown),
        ("T [@\r\n  A] -> U", 3..4, "@", SyntaxKind::Unknown),
        ("T [@/*é*/A] -> U", 3..4, "@", SyntaxKind::Unknown),
        ("T [@/*\n*/A] -> U", 3..4, "@", SyntaxKind::Unknown),
        ("T [@ , A] -> U", 3..4, "@", SyntaxKind::Unknown),
        ("T [A @ B] -> U", 5..6, "@", SyntaxKind::Unknown),
    ] {
        let root = assert_complete_type_recovery(source, 0, &[item(0, range, true)]);
        let error = recovery_groups(&root).into_iter().next().unwrap();
        assert_eq!(error.text(), text, "{source:?}");
        assert_eq!(error.first_token().unwrap().kind(), SyntaxKind::Error);
        assert_eq!(
            error.first_token().unwrap().text(),
            if first == SyntaxKind::Colon { ":" } else { "@" }
        );
        assert_eq!(error.parent().unwrap().kind(), SyntaxKind::BracketRow);
        for retry in error
            .parent()
            .unwrap()
            .children()
            .filter(|node| node.kind() == SyntaxKind::TypeExpression)
        {
            assert!(!retry.text().to_string().starts_with(char::is_whitespace));
        }
    }
    assert_complete_type_recovery("T [@ A] -> U", 40, &[item(0, 43..44, true)]);
}

#[test]
fn bracket_row_missing_and_local_close_slots_publish_in_source_order() {
    for (source, expected) in [
        ("T [,] -> U", vec![item(0, 3..3, false)]),
        (
            "T [)] -> U",
            vec![
                item(0, 3..3, false),
                close(1, 3..4, Some(Delimiter::Parenthesis)),
            ],
        ),
        (
            "T [A)] -> U",
            vec![close(0, 4..5, Some(Delimiter::Parenthesis))],
        ),
        (
            "T [@ )] -> U",
            vec![
                item(0, 3..4, true),
                close(1, 5..6, Some(Delimiter::Parenthesis)),
            ],
        ),
        (
            "T [A))] -> U",
            vec![
                close(0, 4..5, Some(Delimiter::Parenthesis)),
                close(1, 5..6, Some(Delimiter::Parenthesis)),
            ],
        ),
        (
            "T [",
            vec![
                item(0, 3..3, false),
                close(1, 3..3, None),
                arrow(2, 3..3, false),
            ],
        ),
        ("T [A", vec![close(0, 4..4, None), arrow(1, 4..4, false)]),
        (
            "T [@",
            vec![
                item(0, 3..4, true),
                close(1, 4..4, None),
                arrow(2, 4..4, false),
            ],
        ),
        (
            "T [A)",
            vec![
                close(0, 4..5, Some(Delimiter::Parenthesis)),
                close(1, 5..5, None),
                arrow(2, 5..5, false),
            ],
        ),
    ] {
        let root = assert_complete_type_recovery(source, 0, &expected);
        let row = root
            .descendants()
            .find(|node| node.kind() == SyntaxKind::BracketRow)
            .unwrap();
        assert_eq!(
            row.children()
                .filter(|node| node.kind() == SyntaxKind::Missing)
                .count(),
            expected
                .iter()
                .filter(|record| record.kind == RecoveryKind::Missing
                    && record.site.role != GrammarRole::Type(TypeRole::BracketRowArrow))
                .count()
        );
        let groups = recovery_groups(&row);
        let mut expected_ranges: Vec<std::ops::Range<usize>> = Vec::new();
        for record in expected
            .iter()
            .filter(|record| record.kind == RecoveryKind::Error)
        {
            if let Some(last) = expected_ranges
                .last_mut()
                .filter(|last| last.end == record.site.range.start)
            {
                last.end = record.site.range.end;
            } else {
                expected_ranges.push(record.site.range.clone());
            }
        }
        assert_eq!(
            groups
                .iter()
                .map(|group| {
                    assert_eq!(group.parent(), Some(row.clone()));
                    let range = group.text_range();
                    usize::from(range.start()) - "sentinel".len()
                        ..usize::from(range.end()) - "sentinel".len()
                })
                .collect::<Vec<_>>(),
            expected_ranges
        );
        assert_eq!(
            groups.iter().map(|group| group.text()).collect::<Vec<_>>(),
            expected_ranges
                .iter()
                .map(|range| &source[range.clone()])
                .collect::<Vec<_>>()
        );
        for error in row
            .children_with_tokens()
            .filter_map(|element| element.into_token())
            .filter(|token| token.kind() == SyntaxKind::Error && token.text() == ")")
        {
            assert_eq!(error.parent(), Some(row.clone()));
            assert_eq!(error.text_range().len(), 1.into());
        }
    }
    assert_complete_type_recovery(
        "T [A{}] -> U",
        0,
        &[row_record(
            0,
            GrammarRole::Type(TypeRole::BracketRowSeparator),
            ExpectedSyntax::DelimitedSequenceSeparator,
            4..4,
            None,
        )],
    );
    let root =
        assert_complete_type_recovery("F(T [A)", 0, &[close(0, 6..6, None), arrow(1, 6..6, false)]);
    let native = root
        .descendants_with_tokens()
        .find(|child| child.kind() == SyntaxKind::RParen)
        .unwrap();
    assert_eq!(native.parent().unwrap().kind(), SyntaxKind::TypeCallTail);
}

#[test]
fn bracket_row_close_retry_does_not_reenter_the_item_list() {
    for origin in [0, 40] {
        let expected = [
            close(0, origin + 4..origin + 5, Some(Delimiter::Parenthesis)),
            close(1, origin + 5..origin + 5, None),
            arrow(2, origin + 5..origin + 5, false),
        ];
        let frozen = frozen_recovery_ids(&expected);
        for (input, records) in [
            (None, expected.as_slice()),
            (Some(frozen.as_slice()), frozen.as_slice()),
        ] {
            let run = run_contextual_type_snapshot(
                "T [A) B] -> U",
                crate::type_expr::TypeMlContext::INACTIVE,
                0,
                0,
                origin,
                LineEntry::InLine,
                None,
                input,
            );
            assert_eq!(run.green.to_string(), "sentinelT [A)");
            assert_eq!(run.records, records);
            assert_eq!(run.remainder, "] -> U");
            let NormalizedExit::Complete(Err(Either::Left(pending)), line) = run.exit else {
                panic!("close slot keeps following Type pending")
            };
            let (control, control_origin, control_line, remainder, _, _) =
                scan_type_item_control(" B] -> U", origin + 5, &OperatorTable::empty());
            assert_eq!(pending, control);
            assert_eq!(run.successor_origin, control_origin);
            assert_eq!(line, control_line);
            assert_eq!(run.remainder, remainder);
        }
    }
}

#[test]
fn bracket_row_boundaries_preserve_the_complete_current_item_in_every_phase() {
    for (prefix, mut expected) in [
        ("T [", vec![item(0, 3..3, false), close(1, 3..3, None)]),
        ("T [A", vec![close(0, 4..4, None)]),
        ("T [A,", vec![item(0, 5..5, false), close(1, 5..5, None)]),
        ("T [@", vec![item(0, 3..4, true), close(1, 4..4, None)]),
        (
            "T [)",
            vec![
                item(0, 3..3, false),
                close(1, 3..4, Some(Delimiter::Parenthesis)),
                close(2, 4..4, None),
            ],
        ),
    ] {
        expected.push(arrow(
            expected.len() as u32,
            prefix.len()..prefix.len(),
            false,
        ));
        for (payload, stops, outer) in [
            ("else", crate::lexical::stops::STOP_ELSE, 0),
            (":", STOP_COLON, 0),
            (
                "}",
                0,
                crate::type_expr::with_type_outer_close(0, TokenKind::RBrace),
            ),
        ] {
            for gap in [" ", " /*é*/ ", "\n ", "\r\n "] {
                let source = format!("{prefix}{gap}{payload} tail");
                let frozen = frozen_recovery_ids(&expected);
                for (input, records) in [
                    (None, expected.as_slice()),
                    (Some(frozen.as_slice()), frozen.as_slice()),
                ] {
                    let run = run_contextual_type_snapshot(
                        &source,
                        crate::type_expr::TypeMlContext::INACTIVE,
                        stops,
                        outer,
                        0,
                        LineEntry::InLine,
                        None,
                        input,
                    );
                    assert_eq!(
                        run.green.to_string(),
                        format!("sentinel{prefix}"),
                        "{source:?}"
                    );
                    assert_eq!(run.records, records, "{source:?}");
                    assert_eq!(run.slots, records.len());
                    let NormalizedExit::Complete(Err(Either::Left(pending)), line) = run.exit
                    else {
                        panic!("pending row boundary: {source:?}")
                    };
                    let (control, origin, control_line, remainder, _, _) = scan_type_item_control(
                        &source[prefix.len()..],
                        prefix.len(),
                        &OperatorTable::empty(),
                    );
                    assert_eq!(pending, control, "{source:?}");
                    assert_eq!(run.successor_origin, origin);
                    assert_eq!(run.remainder, remainder);
                    assert_eq!(line, control_line);
                    assert!(run.same_operators);
                }
            }
        }
    }
}

#[test]
fn bracket_row_fence_and_structured_pv_keep_native_boundaries() {
    let fence = FenceBoundary {
        opener: FenceOpener {
            line: 0,
            marker: 0..3,
            marker_width: 3,
        },
        prefix_policy: FencePrefixPolicy::ActivePrefixQuote { depth: 2, base: 0 },
        close_column: 0,
    };
    let expected = [
        item(0, 7..8, true),
        close(1, 9..9, None),
        arrow(2, 9..9, false),
    ];
    let frozen = frozen_recovery_ids(&expected);
    for (input, records) in [
        (None, expected.as_slice()),
        (Some(frozen.as_slice()), frozen.as_slice()),
    ] {
        let (green, exit, remainder, actual) = run_type_normalized_with_recoveries(
            "> > T [@\n> > ```\nouter",
            0,
            LineEntry::PhysicalStart,
            Some(&fence),
            input,
        );
        assert_eq!(green.to_string(), "> > T [@");
        assert_eq!(actual, records);
        assert_eq!(remainder, "> > ```\nouter");
        let Some(NormalizedExit::Complete(Err(Either::Left(pending)), LineEntry::PhysicalStart)) =
            exit
        else {
            panic!("row preserves fence")
        };
        assert!(pending.payload_view().is_boundary());
        assert!(pending.leading_view().has_ordinary_newline());
    }
    let root = assert_complete_type_recovery(
        ":{[e] (@ A)}",
        0,
        &[
            expected_type_error(0, TypeRole::PolymorphicVariantTagName, 2..11),
            pe_recovery::item(1, false, 7..8, true),
        ],
    );
    assert!(
        root.descendants()
            .any(|node| node.kind() == SyntaxKind::BracketRow)
    );
    let root = assert_complete_type_recovery(
        ":{[@] T}",
        0,
        &[
            expected_type_error(0, TypeRole::PolymorphicVariantTagName, 2..7),
            item(1, 3..4, true),
        ],
    );
    let error = recovery_groups(&root).into_iter().next().unwrap();
    let crate::tests::recovery_output::RecoveryGroup::Structured(invalid) = error else {
        panic!("structured tag-name Invalid")
    };
    let groups = recovery_groups(&invalid);
    assert_eq!(groups.len(), 2);
    assert_eq!(groups[1].text(), "@");
}
