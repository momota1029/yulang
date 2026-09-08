use super::*;

pub(super) fn arrow(id: u32, range: Range<usize>, error: bool) -> CommittedRecoveryRecord {
    let role = GrammarRole::Type(TypeRole::BracketRowArrow);
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
            expected: ExpectedSyntax::Punctuation(PunctuationEvidence::Arrow),
            range,
            sources: ExpectationSources::COMMITTED_RECOVERY_RULE,
        }]),
        primary_expectation: 0,
    }
}

#[test]
fn bracket_arrow_missing_is_distinct_from_row_close_and_arrow_rhs() {
    for (source, expected) in [
        ("F [e]", vec![arrow(0, 5..5, false)]),
        ("F [e] ", vec![arrow(0, 6..6, false)]),
        ("F [e] U", vec![arrow(0, 6..6, false)]),
        (
            "F [A",
            vec![
                bracket_recovery::close(0, 4..4, None),
                arrow(1, 4..4, false),
            ],
        ),
        (
            "F(T [A)",
            vec![
                bracket_recovery::close(0, 6..6, None),
                arrow(1, 6..6, false),
            ],
        ),
        (
            "F [e] ->",
            vec![expected_type_expression_missing(0, TypeRole::ArrowRhs, 8)],
        ),
    ] {
        assert_complete_type_recovery(source, 0, &expected);
    }
}

#[test]
fn bracket_arrow_errors_retry_arrow_or_rhs_without_an_extra_missing() {
    for (source, range, text) in [
        ("F [e] @ -> U", 6..7, "@"),
        ("F [e] @ U", 6..7, "@"),
        ("F [e] @", 6..7, "@"),
        ("F [e] @ ", 6..7, "@"),
        ("F [e] @ : U", 6..9, "@ :"),
        ("F [e] @/*é*/-> U", 6..7, "@"),
        ("F [e] @\n  -> U", 6..7, "@"),
        ("F [e] @\r\n  U", 6..7, "@"),
    ] {
        let root = assert_complete_type_recovery(source, 0, &[arrow(0, range, true)]);
        let error = root
            .descendants()
            .find(|node| node.kind() == SyntaxKind::Error)
            .unwrap();
        assert_eq!(error.text(), text, "{source:?}");
        assert_eq!(error.parent().unwrap().kind(), SyntaxKind::TypeArrowTail);
        assert!(
            !root
                .descendants()
                .any(|node| node.kind() == SyntaxKind::Missing)
        );
        if text.contains(':') {
            assert!(
                error
                    .children_with_tokens()
                    .any(|child| child.kind() == SyntaxKind::Colon)
            );
        }
    }
    assert_complete_type_recovery(
        "F [e] @ ->",
        0,
        &[
            arrow(0, 6..7, true),
            expected_type_expression_missing(1, TypeRole::ArrowRhs, 10),
        ],
    );
    assert_complete_type_recovery("F [e] @ -> U", 40, &[arrow(0, 46..47, true)]);
}

#[test]
fn bracket_arrow_boundaries_preserve_pending_items_before_and_after_error() {
    for (prefix, expected) in [
        ("F [e]", arrow(0, 5..5, false)),
        ("F [e] @", arrow(0, 6..7, true)),
    ] {
        for (suffix, stops) in [
            (" with tail", crate::parser::operator::STOP_WITH),
            (" /*é*/else tail", crate::parser::operator::STOP_ELSE),
            (" : tail", STOP_COLON),
            (" , tail", 0),
            (" ) tail", 0),
            ("\nU tail", 0),
            ("\r\nU tail", 0),
        ] {
            let source = format!("{prefix}{suffix}");
            let frozen = frozen_recovery_ids(std::slice::from_ref(&expected));
            for (input, records) in [
                (None, std::slice::from_ref(&expected)),
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
                assert_eq!(
                    run.green.to_string(),
                    format!("sentinel{prefix}"),
                    "{source:?}"
                );
                assert_eq!(run.records, records, "{source:?}");
                assert_eq!(run.slots, 1);
                let NormalizedExit::Complete(Err(Either::Left(pending)), line) = run.exit else {
                    panic!("arrow boundary stays pending")
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
    let expected = [arrow(0, 6..7, true)];
    let (green, exit, found, _, remainder, records, _, _) =
        run_required_type_with_outer_boundary_and_recoveries(
            "F [e] @ with tail",
            crate::parser::type_expr::TypeOuterBoundary::WITH,
            false,
            None,
        );
    assert!(found);
    assert_eq!(green.to_string(), "F [e] @");
    assert_eq!(records, expected);
    assert_eq!(remainder, " tail");
    let NormalizedExit::Complete(Err(Either::Left(pending)), _) = exit else {
        panic!("outer contextual boundary stays pending")
    };
    assert_eq!(pending.payload_view().spelling(), Some("with"));
}

#[test]
fn bracket_arrow_fences_and_structured_errors_keep_record_order() {
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
        ("> > F [e]", arrow(0, 10..10, false)),
        ("> > F [e] @", arrow(0, 10..11, true)),
    ] {
        let source = format!("{prefix}\n> > ```\nouter");
        let frozen = frozen_recovery_ids(std::slice::from_ref(&expected));
        for (input, records) in [
            (None, std::slice::from_ref(&expected)),
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
                panic!("arrow preserves fence")
            };
            assert!(pending.payload_view().is_boundary());
            assert!(pending.leading_view().has_ordinary_newline());
        }
    }
    assert_complete_type_recovery(
        ":{123[e] @ -> U}",
        0,
        &[
            expected_type_error(0, TypeRole::PolymorphicVariantTagName, 2..15),
            arrow(1, 9..10, true),
        ],
    );
}

#[test]
fn bracket_arrow_accepted_controls_keep_right_associative_recursion() {
    for source in [
        "F [e] -> U -> V",
        "F [e]\n  -> U",
        "F [e] -> [f] U",
        "[e] F [io] -> U",
    ] {
        let root = assert_complete_type_recovery(source, 0, &[]);
        assert!(
            !root
                .descendants()
                .any(|node| matches!(node.kind(), SyntaxKind::Missing | SyntaxKind::Error))
        );
        assert_eq!(
            root.descendants()
                .filter(|node| node.kind() == SyntaxKind::TypeArrowTail)
                .count(),
            if source.ends_with("-> V") { 2 } else { 1 }
        );
    }
}
