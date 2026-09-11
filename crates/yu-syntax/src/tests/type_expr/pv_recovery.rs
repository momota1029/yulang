use crate::tests::type_expr::*;

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
        let groups = recovery_groups(&root);
        let missing = root
            .descendants()
            .filter(|node| node.kind() == SyntaxKind::Missing)
            .collect::<Vec<_>>();
        assert_eq!(groups.len() + missing.len(), records.len(), "{source:?}");
        for (range, kind) in groups
            .iter()
            .map(|group| (group.text_range(), RecoveryKind::Error))
            .chain(
                missing
                    .iter()
                    .map(|node| (node.text_range(), RecoveryKind::Missing)),
            )
        {
            let range = usize::from(range.start())..usize::from(range.end());
            assert!(
                records
                    .iter()
                    .any(|record| record.site.range == range && record.kind == kind),
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
fn pv_separator_and_foreign_close_errors_have_distinct_cst_slots() {
    let mut direct_shapes = Vec::new();
    for (source, record) in [
        (
            ":{;}",
            expected_record(
                0,
                pv_role(TypeRole::PolymorphicVariantTagSeparator),
                ExpectedSyntax::DelimitedSequenceSeparator,
                2..3,
                Some(UnexpectedCategory::Punctuation(
                    PunctuationEvidence::Semicolon,
                )),
            ),
        ),
        (
            ":{]}",
            expected_record(
                0,
                close_role(),
                ExpectedSyntax::Punctuation(PunctuationEvidence::Close(Delimiter::Brace)),
                2..3,
                Some(UnexpectedCategory::Punctuation(PunctuationEvidence::Close(
                    Delimiter::Bracket,
                ))),
            ),
        ),
    ] {
        let root = assert_complete(source, &[record]);
        let variant = root
            .descendants()
            .find(|node| node.kind() == SyntaxKind::PolymorphicVariantType)
            .expect("polymorphic variant type");
        assert!(
            !variant.descendants().any(|node| {
                matches!(
                    node.kind(),
                    SyntaxKind::Missing | SyntaxKind::Invalid | SyntaxKind::PolymorphicVariantTag
                )
            }),
            "{source:?}"
        );

        let direct = variant.children_with_tokens().collect::<Vec<_>>();
        assert_eq!(direct.len(), 4, "{source:?}");
        if source == ":{;}" {
            assert_eq!(direct[2].kind(), SyntaxKind::Error);
            assert!(direct[2].as_token().is_some());
        } else {
            assert_foreign_closes(&root, &[2..3]);
        }
        assert!(
            !variant
                .descendants()
                .any(|node| node.kind() == SyntaxKind::Error),
            "{source:?}"
        );
        direct_shapes.push(
            direct
                .into_iter()
                .map(|child| {
                    (
                        child.kind(),
                        usize::from(child.text_range().start())
                            ..usize::from(child.text_range().end()),
                    )
                })
                .collect::<Vec<_>>(),
        );
    }

    assert_eq!(
        direct_shapes,
        [
            vec![
                (SyntaxKind::Colon, 0..1),
                (SyntaxKind::LBrace, 1..2),
                (SyntaxKind::Error, 2..3),
                (SyntaxKind::RBrace, 3..4),
            ],
            vec![
                (SyntaxKind::Colon, 0..1),
                (SyntaxKind::LBrace, 1..2),
                (SyntaxKind::PolymorphicVariantForeignClose, 2..3),
                (SyntaxKind::RBrace, 3..4),
            ],
        ]
    );
}

fn assert_foreign_closes(root: &SyntaxNode, ranges: &[Range<usize>]) {
    let wrappers = root
        .descendants()
        .filter(|node| node.kind() == SyntaxKind::PolymorphicVariantForeignClose)
        .collect::<Vec<_>>();
    assert_eq!(wrappers.len(), ranges.len());
    for (wrapper, range) in wrappers.iter().zip(ranges) {
        assert_eq!(
            wrapper.parent().unwrap().kind(),
            SyntaxKind::PolymorphicVariantType
        );
        assert_eq!(
            usize::from(wrapper.text_range().start())..usize::from(wrapper.text_range().end()),
            *range
        );
        let children = wrapper.children_with_tokens().collect::<Vec<_>>();
        assert!(!children.is_empty());
        assert!(
            children
                .iter()
                .all(|child| child.kind() == SyntaxKind::Error && child.as_token().is_some())
        );
        assert_eq!(
            children.first().unwrap().text_range().start(),
            wrapper.text_range().start()
        );
        assert_eq!(
            children.last().unwrap().text_range().end(),
            wrapper.text_range().end()
        );
    }
}

#[test]
fn pv_foreign_close_slots_preserve_positions_leading_and_type_tails() {
    for (prefix, mut records) in [
        (":{", vec![]),
        (":{A", vec![]),
        (":{A,", vec![]),
        (":{,", vec![missing_tag(0, 2)]),
    ] {
        for (close, delimiter) in [(")", Delimiter::Parenthesis), ("]", Delimiter::Bracket)] {
            for leading in ["", " /*é*/", "\r\n"] {
                let start = prefix.len() + leading.len();
                let record = expected_record(
                    records.len() as u32,
                    close_role(),
                    ExpectedSyntax::Punctuation(PunctuationEvidence::Close(Delimiter::Brace)),
                    start..start + 1,
                    Some(UnexpectedCategory::Punctuation(PunctuationEvidence::Close(
                        delimiter,
                    ))),
                );
                records.push(record);
                let source = format!("{prefix}{leading}{close}}}::Next");
                let root = assert_complete(&source, &records);
                assert_foreign_closes(&root, &[start..start + 1]);
                records.pop();
            }
        }
    }
    let root = assert_complete(
        ":{)",
        &[
            expected_record(
                0,
                close_role(),
                ExpectedSyntax::Punctuation(PunctuationEvidence::Close(Delimiter::Brace)),
                2..3,
                Some(UnexpectedCategory::Punctuation(PunctuationEvidence::Close(
                    Delimiter::Parenthesis,
                ))),
            ),
            missing_close(1, 3),
        ],
    );
    assert_foreign_closes(&root, &[2..3]);
}

#[test]
fn pv_mixed_repeated_foreign_closes_keep_separator_groups_direct() {
    let source = ":{;;])];;}";
    let expected = (2..9)
        .map(|at| {
            let (role, expectation, punctuation) = match source.as_bytes()[at] {
                b';' => (
                    pv_role(TypeRole::PolymorphicVariantTagSeparator),
                    ExpectedSyntax::DelimitedSequenceSeparator,
                    PunctuationEvidence::Semicolon,
                ),
                close => (
                    close_role(),
                    ExpectedSyntax::Punctuation(PunctuationEvidence::Close(Delimiter::Brace)),
                    PunctuationEvidence::Close(if close == b']' {
                        Delimiter::Bracket
                    } else {
                        Delimiter::Parenthesis
                    }),
                ),
            };
            expected_record(
                (at - 2) as u32,
                role,
                expectation,
                at..at + 1,
                Some(UnexpectedCategory::Punctuation(punctuation)),
            )
        })
        .collect::<Vec<_>>();
    let frozen = frozen_recovery_ids(&expected);
    let mut fresh = None;
    for (input, records) in [
        (None, expected.as_slice()),
        (Some(frozen.as_slice()), frozen.as_slice()),
    ] {
        let (green, exit, accepted, remainder, actual) =
            run_required_type_with_recoveries(source, 0, LineEntry::InLine, None, input);
        assert!(accepted);
        assert!(matches!(
            exit,
            NormalizedExit::Complete(Err(Either::Right(_)), _)
        ));
        assert_eq!(remainder, "");
        assert_eq!(green.to_string(), source);
        assert_eq!(actual, records);
        let root = SyntaxNode::new_root(green.clone());
        assert_foreign_closes(&root, &[4..5, 5..6, 6..7]);
        let variant = root
            .descendants()
            .find(|node| node.kind() == SyntaxKind::PolymorphicVariantType)
            .unwrap();
        let errors = variant
            .children_with_tokens()
            .filter(|child| child.kind() == SyntaxKind::Error)
            .map(|child| child.to_string())
            .collect::<String>();
        assert_eq!(errors, ";;;;");
        assert_eq!(
            recovery_groups(&root)
                .iter()
                .map(|group| group.text().to_string())
                .collect::<Vec<_>>(),
            [";;", "]", ")", "]", ";;"]
        );
        if let Some(fresh) = &fresh {
            assert_eq!(&green, fresh);
        } else {
            fresh = Some(green);
        }
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
        let error = recovery_groups(&root).into_iter().next().unwrap();
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
            let error = recovery_groups(&root).into_iter().next().unwrap();
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
    use crate::type_expr::TypeMlContext;
    for (prefix, error_start, error_end, role) in [
        (":{@", 2, 3, pv_role(TypeRole::PolymorphicVariantTag)),
        (":{A @", 4, 5, pv_role(TypeRole::PolymorphicVariantPayload)),
        (":{]", 2, 3, close_role()),
    ] {
        for (stop, stops) in [(":", STOP_COLON), ("else", STOP_ELSE)] {
            // Owner dispatch admits `else` as a tag name after a foreign close.
            if role == close_role() && stop == "else" {
                continue;
            }
            let source = format!("{prefix} {stop} rest");
            let error = if role == pv_role(TypeRole::PolymorphicVariantTag) {
                expected_type_error(0, TypeRole::PolymorphicVariantTag, error_start..error_end)
            } else if role == pv_role(TypeRole::PolymorphicVariantPayload) {
                payload_error(0, error_start..error_end)
            } else {
                expected_record(
                    0,
                    close_role(),
                    ExpectedSyntax::Punctuation(PunctuationEvidence::Close(Delimiter::Brace)),
                    error_start..error_end,
                    Some(UnexpectedCategory::Punctuation(PunctuationEvidence::Close(
                        Delimiter::Bracket,
                    ))),
                )
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
                assert_foreign_closes(
                    &SyntaxNode::new_root(run.green.clone()),
                    if prefix == ":{]" { &[10..11] } else { &[] },
                );
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
    let root = assert_complete("F(:{A @ )", &[payload_error(0, 6..7), missing_close(1, 7)]);
    assert_foreign_closes(&root, &[]);
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
    for (source, expected, text, ranges) in [
        (
            "> > :{A @\n> > ```\nouter\n",
            [payload_error(0, 8..9), missing_close(1, 10)],
            "> > :{A @",
            vec![],
        ),
        (
            "> > :{]\n> > ```\nouter\n",
            [
                expected_record(
                    0,
                    close_role(),
                    ExpectedSyntax::Punctuation(PunctuationEvidence::Close(Delimiter::Brace)),
                    6..7,
                    Some(UnexpectedCategory::Punctuation(PunctuationEvidence::Close(
                        Delimiter::Bracket,
                    ))),
                ),
                missing_close(1, 8),
            ],
            "> > :{]",
            vec![6..7],
        ),
    ] {
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
            assert_eq!(green.to_string(), text);
            assert_foreign_closes(&SyntaxNode::new_root(green.clone()), &ranges);
            assert_eq!(records, expected);
            assert_eq!(remainder, "> > ```\nouter\n");
            let Some(NormalizedExit::Complete(Err(Either::Left(pending)), _)) = exit else {
                panic!("fence remains pending")
            };
            assert!(pending.payload_view().is_boundary());
        }
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
        let root = assert_complete(source, &[]);
        assert_foreign_closes(&root, &[]);
    }
}
