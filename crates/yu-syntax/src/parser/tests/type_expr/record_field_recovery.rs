use crate::parser::tests::type_expr::record_sequence_recovery::close;
use crate::parser::tests::type_expr::*;

pub(super) fn field_record(
    id: u32,
    role: TypeRole,
    range: Range<usize>,
    error: bool,
) -> CommittedRecoveryRecord {
    let expected = match role {
        TypeRole::RecordField | TypeRole::RecordFieldName => ExpectedSyntax::Identifier,
        TypeRole::RecordFieldColon => ExpectedSyntax::Punctuation(PunctuationEvidence::Colon),
        TypeRole::RecordFieldType => ExpectedSyntax::TypeExpression,
        TypeRole::RecordFieldSeparator => ExpectedSyntax::DelimitedSequenceSeparator,
        _ => panic!("only named-record field test records"),
    };
    let role = GrammarRole::Type(role);
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
            expected,
            range,
            sources: ExpectationSources::COMMITTED_RECOVERY_RULE,
        }]),
        primary_expectation: 0,
    }
}

#[test]
fn record_field_missing_slots_keep_roles_and_do_not_cascade_colon_into_type() {
    use TypeRole::{RecordFieldColon as C, RecordFieldName as N, RecordFieldType as T};
    for (source, expected) in [
        ("{: A}", vec![field_record(0, N, 1..1, false)]),
        ("{:{b:B}}", vec![field_record(0, N, 1..1, false)]),
        (
            "{:}",
            vec![
                field_record(0, N, 1..1, false),
                field_record(1, T, 2..2, false),
            ],
        ),
        ("{a}", vec![field_record(0, C, 2..2, false)]),
        ("{a }", vec![field_record(0, C, 2..2, false)]),
        ("{a A}", vec![field_record(0, C, 3..3, false)]),
        ("{a :{A}}", vec![field_record(0, C, 6..6, false)]),
        (
            "{a @ :{A}}",
            vec![
                field_record(0, C, 3..4, true),
                field_record(1, C, 8..8, false),
            ],
        ),
        ("{a:}", vec![field_record(0, T, 3..3, false)]),
        ("{a: }", vec![field_record(0, T, 3..3, false)]),
        ("{a:\nb: B}", vec![field_record(0, T, 3..3, false)]),
    ] {
        let root = assert_complete_type_recovery(source, 0, &expected);
        assert_eq!(
            root.descendants()
                .filter(|node| node.kind() == SyntaxKind::Missing)
                .count(),
            expected
                .iter()
                .filter(|record| record.kind == RecoveryKind::Missing)
                .count()
        );
        if source.ends_with(" }") {
            let space = root
                .descendants_with_tokens()
                .filter_map(|element| element.into_token())
                .find(|token| token.kind() == SyntaxKind::Whitespace)
                .unwrap();
            assert_eq!(space.parent().unwrap().kind(), SyntaxKind::NamedRecordType);
        }
        if source.contains(":{A}") {
            assert!(
                !root
                    .descendants()
                    .any(|node| node.kind() == SyntaxKind::PolymorphicVariantType)
            );
            assert_eq!(
                root.descendants()
                    .filter(|node| node.kind() == SyntaxKind::NamedRecordType)
                    .count(),
                2
            );
        }
    }
}

#[test]
fn record_field_errors_publish_exact_slot_extents_and_native_retry_structure() {
    use TypeRole::{RecordFieldColon as C, RecordFieldName as N, RecordFieldType as T};
    for (source, role, range, error_text, first_kind) in [
        ("{@: A}", N, 1..2, "@", SyntaxKind::Unknown),
        ("{@:{b:B}}", N, 1..2, "@", SyntaxKind::Unknown),
        ("{'a: A}", N, 1..3, "'a", SyntaxKind::SigilIdentifier),
        ("{1: A}", N, 1..2, "1", SyntaxKind::Integer),
        ("{@ (): A}", N, 1..5, "@ ()", SyntaxKind::Unknown),
        ("{@ !: A}", N, 1..4, "@ !", SyntaxKind::Unknown),
        ("{a @ : B}", C, 3..4, "@", SyntaxKind::Unknown),
        ("{a @ : :{A}}", C, 3..4, "@", SyntaxKind::Unknown),
        ("{a @:{b:B}}", C, 3..4, "@", SyntaxKind::Unknown),
        ("{a @ B}", C, 3..4, "@", SyntaxKind::Unknown),
        ("{a @}", C, 3..4, "@", SyntaxKind::Unknown),
        ("{a :: B}", C, 3..5, "::", SyntaxKind::ColonColon),
        ("{a = B}", C, 3..4, "=", SyntaxKind::Equals),
        ("{a @\n  B}", C, 3..4, "@", SyntaxKind::Unknown),
        ("{a @\r\n  B}", C, 3..4, "@", SyntaxKind::Unknown),
        ("{a: @ B}", T, 4..5, "@", SyntaxKind::Unknown),
        ("{a: @}", T, 4..5, "@", SyntaxKind::Unknown),
        ("{a: @, b: B}", T, 4..5, "@", SyntaxKind::Unknown),
        ("{a: @\nb: B}", T, 4..5, "@", SyntaxKind::Unknown),
        ("{a: @\n  B}", T, 4..5, "@", SyntaxKind::Unknown),
        ("{a: @/*é*/B}", T, 4..5, "@", SyntaxKind::Unknown),
        ("{a: @ : B}", T, 4..7, "@ :", SyntaxKind::Unknown),
    ] {
        let root = assert_complete_type_recovery(source, 0, &[field_record(0, role, range, true)]);
        let error = root
            .descendants()
            .find(|node| node.kind() == SyntaxKind::Error)
            .unwrap();
        assert_eq!(error.text(), error_text, "{source:?}");
        assert_eq!(error.first_token().unwrap().kind(), first_kind);
        assert_eq!(error.parent().unwrap().kind(), SyntaxKind::TypeRecordField);
        assert!(
            !root
                .descendants()
                .any(|node| node.kind() == SyntaxKind::Missing)
        );
        if source.contains("():") {
            assert!(
                error
                    .children_with_tokens()
                    .any(|child| child.kind() == SyntaxKind::LParen)
            );
            assert!(
                error
                    .children_with_tokens()
                    .any(|child| child.kind() == SyntaxKind::RParen)
            );
        }
    }
    assert_complete_type_recovery("{a: @ B}", 40, &[field_record(0, T, 44..45, true)]);
}

#[test]
fn record_field_caller_words_are_checked_before_fresh_and_recovered_candidates() {
    use TypeRole::{RecordFieldColon as C, RecordFieldType as T};
    for (prefix, expected) in [
        ("{a", field_record(0, C, 2..2, false)),
        ("{a @", field_record(0, C, 3..4, true)),
        ("{a:", field_record(0, T, 3..3, false)),
        ("{a: @", field_record(0, T, 4..5, true)),
    ] {
        for (suffix, stops) in [
            (" with tail", crate::parser::input::operator::STOP_WITH),
            (" /*é*/else tail", crate::parser::input::operator::STOP_ELSE),
        ] {
            let source = format!("{prefix}{suffix}");
            let expected = [
                expected.clone(),
                close(1, prefix.len()..prefix.len(), false),
            ];
            let frozen = frozen_recovery_ids(&expected);
            for (input, records) in [
                (None, expected.as_slice()),
                (Some(frozen.as_slice()), frozen.as_slice()),
            ] {
                let run = run_contextual_type_snapshot(
                    &source,
                    crate::parser::type_expr::TypeMlContext::INACTIVE,
                    stops,
                    0,
                    0,
                    LineEntry::InLine,
                    None,
                    input,
                );
                assert_eq!(run.green.to_string(), format!("sentinel{prefix}"));
                assert_eq!(run.records, records, "{source:?}");
                assert_eq!(run.slots, 2);
                let NormalizedExit::Complete(Err(Either::Left(pending)), line) = run.exit else {
                    panic!("caller Item stays pending")
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
    }
}

#[test]
fn record_field_colon_is_local_only_in_its_own_mandatory_slot() {
    for source in ["{a: A}", "{@: A}", "{a @ : A}", "{a:{b:B}}", "{a: :{B}}"] {
        let (green, exit, records) = run_type_with_context_and_recoveries(
            source,
            crate::parser::type_expr::TypeMlContext::INACTIVE,
            None,
        );
        let contextual = run_contextual_type_snapshot(
            source,
            crate::parser::type_expr::TypeMlContext::INACTIVE,
            STOP_COLON,
            0,
            0,
            LineEntry::InLine,
            None,
            None,
        );
        assert_eq!(contextual.green.to_string(), format!("sentinel{green}"));
        assert_eq!(contextual.records, records);
        assert!(matches!(
            exit,
            NormalizedExit::Complete(Err(Either::Right(_)), _)
        ));
        assert!(matches!(
            contextual.exit,
            NormalizedExit::Complete(Err(Either::Right(_)), _)
        ));
    }
    let run = run_contextual_type_snapshot(
        "{a: : tail",
        crate::parser::type_expr::TypeMlContext::INACTIVE,
        STOP_COLON,
        0,
        0,
        LineEntry::InLine,
        None,
        None,
    );
    assert_eq!(
        run.records,
        [
            field_record(0, TypeRole::RecordFieldType, 3..3, false),
            close(1, 3..3, false)
        ]
    );
    assert_eq!(run.green.to_string(), "sentinel{a:");
    let NormalizedExit::Complete(Err(Either::Left(pending)), _) = run.exit else {
        panic!("RHS colon belongs to caller")
    };
    assert_eq!(pending.payload_view().token_kind(), Some(TokenKind::Colon));
    assert!(!pending.leading_view().is_grammar_empty());

    let run = run_contextual_type_snapshot(
        "{@ (:):A}",
        crate::parser::type_expr::TypeMlContext::INACTIVE,
        STOP_COLON,
        0,
        0,
        LineEntry::InLine,
        None,
        None,
    );
    assert_eq!(
        run.records,
        [
            field_record(0, TypeRole::RecordField, 1..4, true),
            close(1, 4..4, false)
        ]
    );
    assert_eq!(run.green.to_string(), "sentinel{@ (");
    let NormalizedExit::Complete(Err(Either::Left(pending)), _) = run.exit else {
        panic!("a claimed nested colon is not a local name retry")
    };
    assert_eq!(pending.payload_view().token_kind(), Some(TokenKind::Colon));
    assert_eq!(run.remainder, "):A}");
}

#[test]
fn record_field_fence_handoff_keeps_missing_and_error_anchors_truthful() {
    use TypeRole::{RecordFieldColon as C, RecordFieldType as T};
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
        ("> > {a", field_record(0, C, 7..7, false)),
        ("> > {a:", field_record(0, T, 8..8, false)),
        ("> > {a @", field_record(0, C, 7..8, true)),
        ("> > {a: @", field_record(0, T, 8..9, true)),
    ] {
        let source = format!("{prefix}\n> > ```\nouter");
        let at = prefix.len() + 1;
        let expected = [expected, close(1, at..at, false)];
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
            assert_eq!(actual, records);
            assert_eq!(remainder, "> > ```\nouter");
            let Some(NormalizedExit::Complete(
                Err(Either::Left(pending)),
                LineEntry::PhysicalStart,
            )) = exit
            else {
                panic!("field preserves fence")
            };
            assert!(pending.payload_view().is_boundary());
            assert!(pending.leading_view().has_ordinary_newline());
            assert_eq!(
                pending
                    .payload_view()
                    .pending_boundary()
                    .unwrap()
                    .coordinate(),
                prefix.len() + 1
            );
        }
    }
}

#[test]
fn record_field_structured_pv_reservations_order_parent_before_each_nested_slot() {
    use TypeRole::{RecordFieldColon as C, RecordFieldType as T};
    for (source, extent, nested) in [
        (":{{a @ B}}", 2..9, field_record(1, C, 5..6, true)),
        (":{{a: @ B}}", 2..10, field_record(1, T, 6..7, true)),
    ] {
        assert_complete_type_recovery(
            source,
            0,
            &[
                expected_type_error(0, TypeRole::PolymorphicVariantTagName, extent),
                nested,
            ],
        );
    }
}

#[test]
fn record_field_accepted_controls_keep_full_type_and_layout_grammar() {
    for source in [
        "{}",
        "{a: A}",
        "{a:{b:B}}",
        "{a: {b:B}}",
        "{a: :{B}}",
        "{a:[e] B}",
        "{a:'[e]}",
        "{a: A, b: B,}",
        "{a: A\nb: B}",
        "{a:\n  F A}",
        "{a: F(A)::B -> [e] C}",
        "{a: {b: B}, c: for 'a: 'a}",
    ] {
        let root = assert_complete_type_recovery(source, 0, &[]);
        assert!(
            !root
                .descendants()
                .any(|node| matches!(node.kind(), SyntaxKind::Error | SyntaxKind::Missing)),
            "{source:?}"
        );
    }
}

#[test]
fn record_field_next_head_query_shares_exact_colon_ownership() {
    let source = "{a:A b:{c:C}}";
    let root = assert_complete_type_recovery(
        source,
        0,
        &[field_record(0, TypeRole::RecordFieldSeparator, 5..5, false)],
    );
    let record = root
        .descendants()
        .find(|node| node.kind() == SyntaxKind::NamedRecordType)
        .unwrap();
    assert_eq!(
        record
            .children()
            .filter(|node| node.kind() == SyntaxKind::TypeRecordField)
            .count(),
        2
    );
    let missing = record
        .children()
        .find(|node| node.kind() == SyntaxKind::Missing)
        .unwrap();
    assert_eq!(usize::from(missing.text_range().start()), 8 + 5);
    assert!(
        !record
            .descendants()
            .any(|node| node.kind() == SyntaxKind::Error)
    );
    assert_eq!(
        record
            .descendants()
            .filter(|node| node.kind() == SyntaxKind::NamedRecordType)
            .count(),
        2
    );
}
