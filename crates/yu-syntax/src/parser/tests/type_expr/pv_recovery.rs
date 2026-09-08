use crate::parser::tests::type_expr::*;

fn pv_role(role: TypeRole) -> GrammarRole {
    GrammarRole::Type(role)
}

fn close_role() -> GrammarRole {
    GrammarRole::ClosingDelimiter {
        owner: ConstructRole::PolymorphicVariantType,
        delimiter: Delimiter::Brace,
    }
}

fn expected_record(
    id: u32,
    role: GrammarRole,
    expected: ExpectedSyntax,
    range: Range<usize>,
    unexpected: Option<UnexpectedCategory>,
) -> CommittedRecoveryRecord {
    CommittedRecoveryRecord {
        id: DiagnosticId(id),
        site: RecoverySiteKey {
            role,
            range: range.clone(),
        },
        kind: if unexpected.is_some() {
            RecoveryKind::Error
        } else {
            RecoveryKind::Missing
        },
        unexpected: unexpected.map_or_else(
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

fn missing_tag(id: u32, at: usize) -> CommittedRecoveryRecord {
    expected_record(
        id,
        pv_role(TypeRole::PolymorphicVariantTag),
        ExpectedSyntax::Identifier,
        at..at,
        None,
    )
}

fn missing_close(id: u32, at: usize) -> CommittedRecoveryRecord {
    expected_record(
        id,
        close_role(),
        ExpectedSyntax::Punctuation(PunctuationEvidence::Close(Delimiter::Brace)),
        at..at,
        None,
    )
}

fn payload_error(id: u32, range: Range<usize>) -> CommittedRecoveryRecord {
    expected_record(
        id,
        pv_role(TypeRole::PolymorphicVariantPayload),
        ExpectedSyntax::TypeExpression,
        range,
        Some(UnexpectedCategory::OtherCharacter),
    )
}

fn assert_complete(source: &str, expected: &[CommittedRecoveryRecord]) -> SyntaxNode {
    let frozen = frozen_recovery_ids(expected);
    let mut fresh = None;
    for (frozen_input, expected) in [
        (None, expected),
        (Some(frozen.as_slice()), frozen.as_slice()),
    ] {
        let (green, exit, accepted, remainder, records) =
            run_required_type_with_recoveries(source, 0, LineEntry::InLine, None, frozen_input);
        assert!(accepted, "{source:?}");
        assert_eq!(green.to_string(), source, "{source:?}");
        assert_eq!(records, expected, "{source:?}");
        assert!(
            matches!(exit, NormalizedExit::Complete(Err(Either::Right(_)), _)),
            "{source:?}"
        );
        assert_eq!(remainder, "");
        let root = SyntaxNode::new_root(green.clone());
        assert_eq!(
            root.descendants()
                .filter(|node| matches!(node.kind(), SyntaxKind::Error | SyntaxKind::Missing))
                .count(),
            records.len(),
            "{source:?}"
        );
        for node in root
            .descendants()
            .filter(|node| matches!(node.kind(), SyntaxKind::Error | SyntaxKind::Missing))
        {
            let range =
                usize::from(node.text_range().start())..usize::from(node.text_range().end());
            assert!(
                records.iter().any(|record| record.site.range == range
                    && record.kind
                        == if node.kind() == SyntaxKind::Missing {
                            RecoveryKind::Missing
                        } else {
                            RecoveryKind::Error
                        }),
                "{source:?}: {range:?}"
            );
        }
        if let Some(fresh) = &fresh {
            assert_eq!(&green, fresh);
        } else {
            fresh = Some(green);
        }
    }
    SyntaxNode::new_root(fresh.unwrap())
}

#[test]
fn pv_missing_slots_keep_trailing_separator_and_eof_distinct() {
    for (source, records) in [
        (":{,,A}", vec![missing_tag(0, 2), missing_tag(1, 3)]),
        (":{,}", vec![missing_tag(0, 2)]),
        (":{A,}", vec![]),
        (":{A,", vec![missing_tag(0, 4), missing_close(1, 4)]),
        (":{A\n", vec![missing_tag(0, 4), missing_close(1, 4)]),
        (":{A\r\n", vec![missing_tag(0, 5), missing_close(1, 5)]),
        (":{,", vec![missing_tag(0, 2), missing_close(1, 3)]),
        (":{", vec![missing_close(0, 2)]),
        (":{A", vec![missing_close(0, 3)]),
    ] {
        assert_complete(source, &records);
    }
}

#[test]
fn pv_local_punctuation_errors_describe_the_actual_token_and_retry() {
    for (source, range, role, expected, unexpected, close_at) in [
        (
            ":{;A}",
            2..3,
            pv_role(TypeRole::PolymorphicVariantTagSeparator),
            ExpectedSyntax::DelimitedSequenceSeparator,
            PunctuationEvidence::Semicolon,
            None,
        ),
        (
            ":{A ; B}",
            4..5,
            pv_role(TypeRole::PolymorphicVariantTagSeparator),
            ExpectedSyntax::DelimitedSequenceSeparator,
            PunctuationEvidence::Semicolon,
            None,
        ),
        (
            ":{]}",
            2..3,
            close_role(),
            ExpectedSyntax::Punctuation(PunctuationEvidence::Close(Delimiter::Brace)),
            PunctuationEvidence::Close(Delimiter::Bracket),
            None,
        ),
        (
            ":{)",
            2..3,
            close_role(),
            ExpectedSyntax::Punctuation(PunctuationEvidence::Close(Delimiter::Brace)),
            PunctuationEvidence::Close(Delimiter::Parenthesis),
            Some(3),
        ),
    ] {
        let mut records = vec![expected_record(
            0,
            role,
            expected,
            range,
            Some(UnexpectedCategory::Punctuation(unexpected)),
        )];
        if let Some(at) = close_at {
            records.push(missing_close(1, at));
        }
        assert_complete(source, &records);
    }
}

#[test]
fn pv_payload_recovery_keeps_gap_error_and_retry_at_the_payload_owner() {
    let boundary = expected_record(
        0,
        pv_role(TypeRole::PolymorphicVariantPayloadBoundary),
        ExpectedSyntax::TypePayloadBoundary,
        3..3,
        None,
    );
    assert_complete(":{A(Int)}", &[boundary]);
    for (source, range, text) in [
        (":{A @ Int}", 4..5, "@"),
        (":{A @/*é*/Int}", 4..5, "@"),
        (":{A @ . Int}", 4..7, "@ ."),
        (":{α @β}", 5..6, "@"),
        (":{A @,B}", 4..5, "@"),
    ] {
        let root = assert_complete(source, &[payload_error(0, range)]);
        let error = root
            .descendants()
            .find(|node| node.kind() == SyntaxKind::Error)
            .unwrap();
        assert_eq!(error.text(), text);
        assert_eq!(
            error.parent().unwrap().kind(),
            SyntaxKind::PolymorphicVariantPayload
        );
    }
}

#[test]
fn pv_boundaryless_malformed_items_retry_in_a_new_tag_without_lookahead() {
    for source in [":{A@Int}", ":{A@}", ":{A@ Int}"] {
        let root = assert_complete(
            source,
            &[expected_type_error(
                0,
                TypeRole::PolymorphicVariantTag,
                3..4,
            )],
        );
        let variant = root
            .descendants()
            .find(|node| node.kind() == SyntaxKind::PolymorphicVariantType)
            .unwrap();
        let tags = variant
            .children()
            .filter(|node| node.kind() == SyntaxKind::PolymorphicVariantTag)
            .collect::<Vec<_>>();
        assert_eq!(tags.len(), 2);
        assert_eq!(tags[0].text(), "A");
        assert!(
            !variant
                .descendants()
                .any(|node| node.kind() == SyntaxKind::PolymorphicVariantPayload)
        );
        if source.contains("Int") {
            assert!(
                tags[1]
                    .children_with_tokens()
                    .any(|child| child.kind() == SyntaxKind::Identifier
                        && child.to_string() == "Int")
            );
        }
    }
}

#[test]
fn pv_wrong_kind_type_keeps_tight_tails_and_structured_record_order() {
    for (body, end, owner) in [
        (":{123::T}", 8, SyntaxKind::TypePathTail),
        (":{123->T}", 8, SyntaxKind::TypeArrowTail),
        (":{(A)(B)}", 8, SyntaxKind::TypeCallTail),
        (":{'[A](B)}", 9, SyntaxKind::TypeCallTail),
        (":{[e] T}", 7, SyntaxKind::BracketRow),
    ] {
        for suffix in ["", "::Next"] {
            let source = format!("{body}{suffix}");
            let root = assert_complete(
                &source,
                &[expected_type_error(
                    0,
                    TypeRole::PolymorphicVariantTagName,
                    2..end,
                )],
            );
            let error = root
                .descendants()
                .find(|node| node.kind() == SyntaxKind::Error)
                .unwrap();
            assert!(error.descendants().any(|node| node.kind() == owner));
            assert_eq!(error.text().to_string(), source[2..end]);
            let top = root
                .children()
                .find(|node| node.kind() == SyntaxKind::TypeExpression)
                .unwrap();
            assert_eq!(
                top.children()
                    .filter(|node| node.kind() == SyntaxKind::TypePathTail)
                    .count(),
                usize::from(!suffix.is_empty())
            );
        }
    }
    assert_complete(
        ":{:{A",
        &[
            expected_type_error(0, TypeRole::PolymorphicVariantTagName, 2..5),
            missing_close(1, 5),
            missing_close(2, 5),
        ],
    );
}

#[test]
fn pv_malformed_run_returns_complete_caller_item_before_retry() {
    use crate::parser::type_expr::TypeMlContext;
    for (prefix, error_start, error_end, role) in [
        (":{@", 2, 3, TypeRole::PolymorphicVariantTag),
        (":{A @", 4, 5, TypeRole::PolymorphicVariantPayload),
    ] {
        for (stop, stops) in [(":", STOP_COLON), ("else", STOP_ELSE)] {
            let source = format!("{prefix} {stop} rest");
            let error = if role == TypeRole::PolymorphicVariantTag {
                expected_type_error(0, role, error_start..error_end)
            } else {
                payload_error(0, error_start..error_end)
            };
            let expected = [error, missing_close(1, error_end)];
            let frozen = frozen_recovery_ids(&expected);
            for (input, expected) in [
                (None, expected.as_slice()),
                (Some(frozen.as_slice()), frozen.as_slice()),
            ] {
                let run = run_contextual_type_snapshot(
                    &source,
                    TypeMlContext::INACTIVE,
                    stops,
                    0,
                    0,
                    LineEntry::InLine,
                    None,
                    input,
                );
                assert_eq!(run.green.to_string(), format!("sentinel{prefix}"));
                assert_eq!(run.records, expected);
                assert_eq!(run.remainder, " rest");
                assert_eq!(run.successor_origin, prefix.len() + 1 + stop.len());
                assert_eq!(run.slots, 2);
                let NormalizedExit::Complete(Err(Either::Left(mut pending)), _) = run.exit else {
                    panic!("caller stop must remain pending")
                };
                assert_eq!(pending.payload_view().spelling(), Some(stop));
                assert_eq!(emit_pending_leading_text(&mut pending), " ");
            }
        }
    }
}

#[test]
fn pv_close_records_preserve_native_outer_closes_and_shifted_coordinates() {
    assert_complete("F(:{A @ )", &[payload_error(0, 6..7), missing_close(1, 7)]);
    let expected = [payload_error(0, 44..45)];
    assert_complete_type_recovery(":{A @ Int}", 40, &expected);

    let fence = FenceBoundary {
        opener: FenceOpener {
            line: 0,
            marker: 0..3,
            marker_width: 3,
        },
        prefix_policy: FencePrefixPolicy::ActivePrefixQuote { depth: 2, base: 0 },
        close_column: 0,
    };
    let source = "> > :{A @\n> > ```\nouter\n";
    let expected = [payload_error(0, 8..9), missing_close(1, 10)];
    let frozen = frozen_recovery_ids(&expected);
    for (input, expected) in [
        (None, expected.as_slice()),
        (Some(frozen.as_slice()), frozen.as_slice()),
    ] {
        let (green, exit, remainder, records) = run_type_normalized_with_recoveries(
            source,
            0,
            LineEntry::PhysicalStart,
            Some(&fence),
            input,
        );
        assert_eq!(green.to_string(), "> > :{A @");
        assert_eq!(records, expected);
        assert_eq!(remainder, "> > ```\nouter\n");
        let Some(NormalizedExit::Complete(Err(Either::Left(pending)), _)) = exit else {
            panic!("fence remains pending")
        };
        assert!(pending.payload_view().is_boundary());
    }
}

#[test]
fn pv_formally_accepted_controls_have_no_recovery_or_missing_structure() {
    // Standalone PV grammar: comma/newline tags, horizontal Type-ML payloads.
    for source in [
        ":{}",
        ":{a}",
        ":{A Int, B}",
        ":{A Int Bool}",
        ":{A Int\nB}",
        ":{A,}",
        ":{A [e] T X}",
        ":{A Pair(Int, Bool)}",
        ":{A Int/*é*/Bool}",
    ] {
        assert_complete(source, &[]);
    }
}
