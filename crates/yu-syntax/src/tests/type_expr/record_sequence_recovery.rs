use crate::tests::type_expr::record_field_recovery::field_record;
use crate::tests::type_expr::*;

pub(super) fn close(id: u32, range: Range<usize>, error: bool) -> CommittedRecoveryRecord {
    let role = GrammarRole::ClosingDelimiter {
        owner: ConstructRole::NamedRecordType,
        delimiter: Delimiter::Brace,
    };
    CommittedRecoveryRecord {
        id: DiagnosticId(id),
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
            expected: ExpectedSyntax::Punctuation(PunctuationEvidence::Close(Delimiter::Brace)),
            range,
            sources: ExpectationSources::COMMITTED_RECOVERY_RULE,
        }]),
        primary_expectation: 0,
    }
}

fn assert_typed_nodes(root: &SyntaxNode, expected: &[CommittedRecoveryRecord]) {
    for record in root
        .descendants()
        .filter(|node| node.kind() == SyntaxKind::NamedRecordType)
    {
        let closes: Vec<_> = record
            .children()
            .filter(|node| node.kind() == SyntaxKind::NamedRecordTypeClose)
            .collect();
        assert_eq!(closes.len(), 1, "{}", root.text());
        assert!(matches!(
            closes[0].last_child_or_token().unwrap().kind(),
            SyntaxKind::RBrace | SyntaxKind::Missing
        ));
    }
    for (syntax, recovery) in [
        (SyntaxKind::Missing, RecoveryKind::Missing),
        (SyntaxKind::Error, RecoveryKind::Error),
    ] {
        assert_eq!(
            if syntax == SyntaxKind::Error {
                recovery_groups(root).len()
            } else {
                root.descendants()
                    .filter(|node| node.kind() == syntax)
                    .count()
            },
            expected
                .iter()
                .filter(|record| record.kind == recovery)
                .count(),
            "{}",
            root.text(),
        );
    }
}

#[test]
fn record_accepted_closes_have_one_slot_and_commas_remain_native() {
    for source in ["{}", "{ }", "{a:A, b:B,}", "{a:A\nb:B}", "{a:{b:B}}"] {
        let root = assert_complete_type_recovery(source, 0, &[]);
        assert_typed_nodes(&root, &[]);
        assert!(
            !root
                .descendants()
                .any(|node| node.kind() == SyntaxKind::NamedRecordTypeSeparator)
        );
        for token in root
            .descendants_with_tokens()
            .filter_map(|element| element.into_token())
        {
            if token.kind() == SyntaxKind::Comma {
                assert_eq!(token.parent().unwrap().kind(), SyntaxKind::NamedRecordType);
            }
            if token.kind() == SyntaxKind::RBrace {
                assert_eq!(
                    token.parent().unwrap().kind(),
                    SyntaxKind::NamedRecordTypeClose
                );
            }
        }
    }
}

#[test]
fn record_separator_error_slots_preserve_initial_leading_and_field_errors() {
    use TypeRole::{RecordField as F, RecordFieldSeparator as S};
    for (source, expected, separator) in [
        ("{;}", vec![field_record(0, S, 1..2, true)], ";"),
        ("{ ;}", vec![field_record(0, S, 2..3, true)], ";"),
        ("{a:A,;}", vec![field_record(0, S, 5..6, true)], ";"),
        ("{a:A ; b:B}", vec![field_record(0, S, 5..6, true)], ";"),
    ] {
        let root = assert_complete_type_recovery(source, 0, &expected);
        assert_typed_nodes(&root, &expected);
        let slots: Vec<_> = root
            .descendants()
            .filter(|node| node.kind() == SyntaxKind::NamedRecordTypeSeparator)
            .collect();
        assert_eq!(slots.len(), 1);
        assert_eq!(slots[0].text(), separator);
        assert!(
            slots[0]
                .children_with_tokens()
                .all(|element| element.kind() == SyntaxKind::Error)
        );
        if source.contains(" ;") {
            assert_eq!(
                slots[0].prev_sibling_or_token().unwrap().kind(),
                SyntaxKind::Whitespace
            );
        }
    }
    // A semicolon inside an already committed Field run stays in that run.
    let expected = [field_record(0, F, 1..3, true)];
    let root = assert_complete_type_recovery("{@;}", 0, &expected);
    assert_typed_nodes(&root, &expected);
    assert!(
        !root
            .descendants()
            .any(|node| node.kind() == SyntaxKind::NamedRecordTypeSeparator)
    );
    let groups = recovery_groups(&root);
    assert_eq!(groups.len(), 1);
    assert_eq!(groups[0].text(), "@;");
    assert_eq!(
        groups[0].parent().unwrap().kind(),
        SyntaxKind::NamedRecordType
    );
}

#[test]
fn record_close_slot_distinguishes_fresh_and_committed_eof_leading() {
    use TypeRole::RecordField as F;
    for (source, expected, close_text, direct_missing) in [
        ("{", vec![close(0, 1..1, false)], "", false),
        ("{  ", vec![close(0, 3..3, false)], "", false),
        (
            "{a:A,  ",
            vec![field_record(0, F, 7..7, false), close(1, 7..7, false)],
            "",
            true,
        ),
        (
            "{a:A]  ",
            vec![close(0, 4..5, true), close(1, 7..7, false)],
            "]  ",
            false,
        ),
        (
            "{a:A,]  ",
            vec![
                field_record(0, F, 5..5, false),
                close(1, 5..6, true),
                close(2, 8..8, false),
            ],
            "]  ",
            true,
        ),
    ] {
        let root = assert_complete_type_recovery(source, 0, &expected);
        assert_typed_nodes(&root, &expected);
        let slot = root
            .descendants()
            .find(|node| node.kind() == SyntaxKind::NamedRecordTypeClose)
            .unwrap();
        assert_eq!(slot.text(), close_text, "{source:?}");
        assert_eq!(
            slot.prev_sibling_or_token()
                .is_some_and(|element| element.kind() == SyntaxKind::Missing),
            direct_missing,
            "{source:?}"
        );
    }
}

#[test]
fn record_sequence_missing_slots_are_typed_and_nested_closes_are_not_deduplicated() {
    use TypeRole::{RecordField as F, RecordFieldSeparator as S};
    for origin in [0, 41] {
        for (source, expected) in [
            (
                "{,a:A}",
                vec![field_record(0, F, origin + 1..origin + 1, false)],
            ),
            (
                "{a:A,,b:B}",
                vec![field_record(0, F, origin + 5..origin + 5, false)],
            ),
            (
                "{a:A b:B}",
                vec![field_record(0, S, origin + 5..origin + 5, false)],
            ),
            (
                "{a:A b:{c:C}}",
                vec![field_record(0, S, origin + 5..origin + 5, false)],
            ),
            ("{", vec![close(0, origin + 1..origin + 1, false)]),
            ("{a:A", vec![close(0, origin + 4..origin + 4, false)]),
            (
                "{a:A,",
                vec![
                    field_record(0, F, origin + 5..origin + 5, false),
                    close(1, origin + 5..origin + 5, false),
                ],
            ),
            (
                "{a:{b:B",
                vec![
                    close(0, origin + 7..origin + 7, false),
                    close(1, origin + 7..origin + 7, false),
                ],
            ),
        ] {
            let root = assert_complete_type_recovery(source, origin, &expected);
            assert_typed_nodes(&root, &expected);
            if source.starts_with("{a:A b:") {
                let separator = root
                    .descendants()
                    .find(|node| node.kind() == SyntaxKind::NamedRecordTypeSeparator)
                    .unwrap();
                assert_eq!(
                    separator
                        .children()
                        .map(|node| node.kind())
                        .collect::<Vec<_>>(),
                    [SyntaxKind::Missing]
                );
                assert_eq!(
                    separator.prev_sibling_or_token().unwrap().kind(),
                    SyntaxKind::Whitespace
                );
            }
        }
    }
}

#[test]
fn record_sequence_and_name_errors_keep_their_cut_and_native_nested_items() {
    use TypeRole::{RecordField as F, RecordFieldName as N, RecordFieldSeparator as S};
    for (source, role, range, text) in [
        ("{@ a:A}", F, 1..2, "@"),
        ("{..A,b:B}", F, 1..4, "..A"),
        ("{@\nb:B}", F, 1..2, "@"),
        ("{@ (\nb:B}", F, 1..4, "@ ("),
        ("{@:A}", N, 1..2, "@"),
        ("{():A}", N, 1..3, "()"),
        ("{(:):A}", N, 1..4, "(:)"),
        ("{a:A; b:B}", S, 4..5, ";"),
        ("{a:A; (\n) b:B}", S, 4..9, "; (\n)"),
        ("{a:A; /*é*/ b:B}", S, 4..5, ";"),
    ] {
        let expected = [field_record(0, role, range, true)];
        let root = assert_complete_type_recovery(source, 0, &expected);
        assert_typed_nodes(&root, &expected);
        let error = recovery_groups(&root).into_iter().next().unwrap();
        assert_eq!(error.text(), text, "{source:?}");
        assert_eq!(
            error.parent().unwrap().kind(),
            if role == N {
                SyntaxKind::TypeRecordField
            } else if role == S {
                SyntaxKind::NamedRecordTypeSeparator
            } else {
                SyntaxKind::NamedRecordType
            }
        );
        if text.contains('(') {
            assert!(
                error
                    .children_with_tokens()
                    .filter_map(|element| element.into_token())
                    .any(|token| token.kind() == SyntaxKind::Error && token.text() == "(")
            );
        }
    }
    // A ')' cannot discharge the '[' in a malformed name authority probe.
    let expected = [field_record(0, F, 1..3, true), close(1, 3..7, true)];
    let root = assert_complete_type_recovery("{([)]:A}", 0, &expected);
    // The approved close slot preserves the Field/Close record boundary.
    let groups = recovery_groups(&root);
    assert_eq!(groups.len(), 2);
    assert_eq!(groups[0].text(), "([");
    assert_eq!(groups[1].text(), ")]:A");
    assert_eq!(
        groups[1].parent().unwrap().kind(),
        SyntaxKind::NamedRecordTypeClose
    );
    assert_eq!(
        groups[1].text_range(),
        rowan::TextRange::new(11.into(), 15.into())
    );
    assert_eq!(
        groups[0].parent().unwrap().kind(),
        SyntaxKind::NamedRecordType
    );
    assert_eq!(
        groups[0].text_range(),
        rowan::TextRange::new(9.into(), 11.into())
    );
    assert!(matches!(
        groups[0],
        crate::tests::recovery_output::RecoveryGroup::Raw(_)
    ));
    assert!(
        !root
            .descendants()
            .any(|node| node.kind() == SyntaxKind::Missing)
    );
    assert!(
        !root
            .descendants()
            .any(|node| node.kind() == SyntaxKind::TypeRecordField)
    );
}

#[test]
fn record_unclaimed_closes_use_one_native_close_only_run_and_preserve_outer_tails() {
    use TypeRole::RecordField as F;
    for origin in [0, 41] {
        for (source, expected) in [
            ("{a:A]}", vec![close(0, origin + 4..origin + 5, true)]),
            ("{a:A]}::Next", vec![close(0, origin + 4..origin + 5, true)]),
            (
                "{a:A]",
                vec![
                    close(0, origin + 4..origin + 5, true),
                    close(1, origin + 5..origin + 5, false),
                ],
            ),
            ("{a:A] junk}", vec![close(0, origin + 4..origin + 10, true)]),
            (
                "F({a:A])",
                vec![
                    close(0, origin + 6..origin + 7, true),
                    close(1, origin + 7..origin + 7, false),
                ],
            ),
            (
                "{a:A,]",
                vec![
                    field_record(0, F, origin + 5..origin + 5, false),
                    close(1, origin + 5..origin + 6, true),
                    close(2, origin + 6..origin + 6, false),
                ],
            ),
        ] {
            let root = assert_complete_type_recovery(source, origin, &expected);
            assert_typed_nodes(&root, &expected);
            let error = recovery_groups(&root).into_iter().next().unwrap();
            assert_eq!(error.first_token().unwrap().kind(), SyntaxKind::Error);
            assert_eq!(error.first_token().unwrap().text(), "]");
            assert_eq!(
                error.parent().unwrap().kind(),
                SyntaxKind::NamedRecordTypeClose
            );
            assert!(
                !error
                    .descendants_with_tokens()
                    .filter_map(|element| element.into_token())
                    .any(|token| token.text() == "}")
            );
            if source.ends_with("::Next") {
                let tail = root
                    .descendants()
                    .find(|node| node.kind() == SyntaxKind::TypePathTail)
                    .unwrap();
                assert_eq!(tail.text(), "::Next");
                assert!(
                    !tail
                        .ancestors()
                        .any(|node| matches!(node.kind(), SyntaxKind::Error | SyntaxKind::Invalid))
                );
            }
            if source.starts_with("F(") {
                let close = root
                    .descendants_with_tokens()
                    .filter_map(|element| element.into_token())
                    .find(|token| token.kind() == SyntaxKind::RParen)
                    .unwrap();
                assert_eq!(close.parent().unwrap().kind(), SyntaxKind::TypeCallClose);
                assert_eq!(
                    close.parent().unwrap().parent().unwrap().kind(),
                    SyntaxKind::TypeCallTail
                );
            }
        }
    }
}

fn assert_pending_record(
    prefix: &str,
    suffix: &str,
    stops: Stops,
    outer_closes: u8,
    expected: &[CommittedRecoveryRecord],
) {
    let source = format!("{prefix}{suffix}");
    let frozen = frozen_recovery_ids(expected);
    for (input, records) in [
        (None, expected),
        (Some(frozen.as_slice()), frozen.as_slice()),
    ] {
        let run = run_contextual_type_snapshot(
            &source,
            crate::type_expr::TypeMlContext::INACTIVE,
            stops,
            outer_closes,
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
        assert_typed_nodes(&SyntaxNode::new_root(run.green), records);
        let NormalizedExit::Complete(Err(Either::Left(pending)), line) = run.exit else {
            panic!("complete caller Item must remain pending: {source:?}")
        };
        let (control, origin, control_line, remainder, _, _) =
            scan_type_item_control(suffix, prefix.len(), &OperatorTable::empty());
        assert_eq!(pending, control, "{source:?}");
        assert_eq!(run.successor_origin, origin);
        assert_eq!(run.remainder, remainder);
        assert_eq!(line, control_line);
        assert_eq!(run.mark, ());
        assert!(run.same_operators);
    }
}

#[test]
fn record_caller_and_inherited_close_boundaries_keep_the_complete_pending_item() {
    use TypeRole::{RecordField as F, RecordFieldSeparator as S};
    for (prefix, expected) in [
        ("{", vec![close(0, 1..1, false)]),
        ("{a:A", vec![close(0, 4..4, false)]),
        (
            "{a:A,",
            vec![field_record(0, F, 5..5, false), close(1, 5..5, false)],
        ),
        (
            "{@",
            vec![field_record(0, F, 1..2, true), close(1, 2..2, false)],
        ),
        (
            "{a:A;",
            vec![field_record(0, S, 4..5, true), close(1, 5..5, false)],
        ),
        ("{a:A]", vec![close(0, 4..5, true), close(1, 5..5, false)]),
    ] {
        assert_pending_record(
            prefix,
            " /*é*/with tail",
            crate::lexical::stops::STOP_WITH,
            0,
            &expected,
        );
        let inherited = crate::type_expr::with_type_outer_close(0, TokenKind::RParen);
        assert_pending_record(prefix, " /*é*/) tail", 0, inherited, &expected);
    }
    let inherited = crate::type_expr::with_type_outer_close(0, TokenKind::RBracket);
    assert_pending_record("{a:A", " ] tail", 0, inherited, &[close(0, 4..4, false)]);
    assert_pending_record(
        "{a:A,",
        "] tail",
        0,
        inherited,
        &[field_record(0, F, 5..5, false), close(1, 5..5, false)],
    );
    assert_pending_record(
        "{a:A",
        "\nwith tail",
        crate::lexical::stops::STOP_WITH,
        0,
        &[field_record(0, F, 4..4, false), close(1, 4..4, false)],
    );
}

#[test]
fn record_name_authority_and_nested_recovery_do_not_cross_caller_stops() {
    use TypeRole::{RecordField as F, RecordFieldSeparator as S};
    for (suffix, stops) in [
        (":):A}", STOP_COLON),
        ("with):A}", crate::lexical::stops::STOP_WITH),
        ("with:A)}", crate::lexical::stops::STOP_WITH),
        (",b:B)}", crate::lexical::stops::STOP_COMMA),
    ] {
        assert_pending_record(
            "{@ (",
            suffix,
            stops,
            0,
            &[field_record(0, F, 1..4, true), close(1, 4..4, false)],
        );
    }
    assert_pending_record(
        "{@ {",
        "} tail",
        stops_for(TokenKind::RBrace),
        0,
        &[field_record(0, F, 1..4, true), close(1, 4..4, false)],
    );
    assert_pending_record(
        "{a:A",
        "; tail",
        crate::lexical::stops::STOP_SEMICOLON,
        0,
        &[close(0, 4..4, false)],
    );
    assert_pending_record(
        "{a:A; (",
        "\nwith tail",
        crate::lexical::stops::STOP_WITH,
        0,
        &[
            field_record(0, S, 4..7, true),
            field_record(1, F, 7..7, false),
            close(2, 7..7, false),
        ],
    );
}

#[test]
fn record_sequence_fence_handoff_records_each_slot_without_consuming_leading() {
    use TypeRole::{RecordField as F, RecordFieldSeparator as S};
    let fence = FenceBoundary {
        opener: FenceOpener {
            line: 0,
            marker: 0..3,
            marker_width: 3,
        },
        prefix_policy: FencePrefixPolicy::ActivePrefixQuote { depth: 2, base: 0 },
        close_column: 0,
    };
    for (prefix, expected) in [
        ("> > {", vec![close(0, 6..6, false)]),
        (
            "> > {a:A,",
            vec![field_record(0, F, 10..10, false), close(1, 10..10, false)],
        ),
        (
            "> > {@",
            vec![field_record(0, F, 5..6, true), close(1, 7..7, false)],
        ),
        (
            "> > {a:A;",
            vec![field_record(0, S, 8..9, true), close(1, 10..10, false)],
        ),
        (
            "> > {a:A]",
            vec![close(0, 8..9, true), close(1, 10..10, false)],
        ),
        (
            "> > {a:A,]",
            vec![
                field_record(0, F, 9..9, false),
                close(1, 9..10, true),
                close(2, 11..11, false),
            ],
        ),
    ] {
        let source = format!("{prefix}\n> > ```\nouter");
        let frozen = frozen_recovery_ids(&expected);
        for (input, records) in [
            (None, expected.as_slice()),
            (Some(frozen.as_slice()), frozen.as_slice()),
        ] {
            let (green, exit, remainder, actual) = run_type_normalized_with_recoveries(
                &source,
                0,
                LineEntry::PhysicalStart,
                Some(&fence),
                input,
            );
            assert_eq!(green.to_string(), prefix);
            assert_eq!(actual, records, "{prefix:?}");
            let root = SyntaxNode::new_root(green);
            assert_typed_nodes(&root, records);
            if prefix.ends_with(']') {
                let slot = root
                    .descendants()
                    .find(|node| node.kind() == SyntaxKind::NamedRecordTypeClose)
                    .unwrap();
                assert_eq!(slot.text(), "]");
                assert_eq!(
                    slot.children_with_tokens()
                        .map(|element| element.kind())
                        .collect::<Vec<_>>(),
                    [SyntaxKind::Error, SyntaxKind::Missing]
                );
                assert_eq!(
                    slot.prev_sibling_or_token()
                        .is_some_and(|element| element.kind() == SyntaxKind::Missing),
                    prefix.ends_with(",]")
                );
            }
            assert_eq!(remainder, "> > ```\nouter");
            let Some(NormalizedExit::Complete(Err(Either::Left(item)), LineEntry::PhysicalStart)) =
                exit
            else {
                panic!("record must preserve the fence Item")
            };
            assert!(item.payload_view().is_boundary());
            assert!(item.leading_view().has_ordinary_newline());
            assert_eq!(
                item.payload_view().pending_boundary().unwrap().coordinate(),
                prefix.len() + 1
            );
        }
    }
}

#[test]
fn record_eof_newline_opens_a_distinct_field_slot_and_stays_outside_the_record() {
    use TypeRole::RecordField as F;
    for (source, at) in [("{a:A\n", 4), ("{a:A,\n", 5)] {
        let expected = [field_record(0, F, at..at, false), close(1, at..at, false)];
        let frozen = frozen_recovery_ids(&expected);
        for (input, records) in [
            (None, expected.as_slice()),
            (Some(frozen.as_slice()), frozen.as_slice()),
        ] {
            let run = run_contextual_type_snapshot(
                source,
                crate::type_expr::TypeMlContext::INACTIVE,
                0,
                0,
                0,
                LineEntry::InLine,
                None,
                input,
            );
            assert_eq!(run.green.to_string(), format!("sentinel{source}"));
            assert_eq!(run.records, records);
            assert_eq!(run.successor_origin, source.len());
            assert_eq!(run.remainder, "");
            let NormalizedExit::Complete(Err(Either::Right(_)), line) = run.exit else {
                panic!("record must return the EOF Item")
            };
            let (_, _, control_line, _, _, _) =
                scan_type_item_control("\n", at, &OperatorTable::empty());
            assert_eq!(line, control_line);
            let root = SyntaxNode::new_root(run.green);
            assert_typed_nodes(&root, records);
            let newline = root
                .descendants_with_tokens()
                .filter_map(|element| element.into_token())
                .find(|token| token.kind() == SyntaxKind::Newline)
                .unwrap();
            assert_eq!(newline.parent().unwrap().kind(), SyntaxKind::Root);
        }
    }
}

#[test]
fn record_sequence_records_remain_inside_ordered_structured_pv_reservations() {
    use TypeRole::{RecordField as F, RecordFieldSeparator as S};
    for (source, extent, nested) in [
        (":{{@}}", 2..5, field_record(1, F, 3..4, true)),
        (":{{a:A; b:B}}", 2..12, field_record(1, S, 6..7, true)),
        (":{{a:A]}}", 2..8, close(1, 6..7, true)),
    ] {
        let expected = [
            expected_type_error(0, TypeRole::PolymorphicVariantTagName, extent),
            nested,
        ];
        let root = assert_complete_type_recovery(source, 0, &expected);
        assert_typed_nodes(&root, &expected);
    }
}

#[test]
fn record_local_skeletons_and_punctuation_keep_accepted_caller_contexts() {
    let stops = crate::lexical::stops::STOP_WITH | STOP_COLON | stops_for(TokenKind::RBrace);
    for source in [
        "{}",
        "{a:A, b:B,}",
        "{with:A}",
        "{\nwith:A\n}",
        "{a:A\nwith:B}",
        "{a:{b:B}}",
    ] {
        let run = run_contextual_type_snapshot(
            source,
            crate::type_expr::TypeMlContext::INACTIVE,
            stops,
            0,
            0,
            LineEntry::InLine,
            None,
            None,
        );
        assert_eq!(run.green.to_string(), format!("sentinel{source}"));
        assert_eq!(run.records, [], "{source:?}");
        assert!(matches!(
            run.exit,
            NormalizedExit::Complete(Err(Either::Right(_)), _)
        ));
        assert_typed_nodes(&SyntaxNode::new_root(run.green), &[]);
    }
}
