use crate::tests::type_expr::*;

fn recovery(
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
    effect: bool,
    range: Range<usize>,
    category: Option<UnexpectedCategory>,
) -> CommittedRecoveryRecord {
    let (owner, delimiter) = if effect {
        (ConstructRole::EffectRowType, Delimiter::Bracket)
    } else {
        (
            ConstructRole::ParenthesizedTypeGroup,
            Delimiter::Parenthesis,
        )
    };
    recovery(
        id,
        GrammarRole::ClosingDelimiter { owner, delimiter },
        ExpectedSyntax::Punctuation(PunctuationEvidence::Close(delimiter)),
        range,
        category,
    )
}

pub(super) fn item(
    id: u32,
    effect: bool,
    range: Range<usize>,
    error: bool,
) -> CommittedRecoveryRecord {
    recovery(
        id,
        GrammarRole::Type(if effect {
            TypeRole::EffectRowItem
        } else {
            TypeRole::ParenthesizedItem
        }),
        ExpectedSyntax::TypeExpression,
        range,
        error.then_some(UnexpectedCategory::OtherCharacter),
    )
}

pub(super) fn separator(id: u32, effect: bool, at: usize) -> CommittedRecoveryRecord {
    recovery(
        id,
        GrammarRole::Type(if effect {
            TypeRole::EffectRowSeparator
        } else {
            TypeRole::ParenthesizedSeparator
        }),
        ExpectedSyntax::DelimitedSequenceSeparator,
        at..at,
        None,
    )
}

#[test]
fn pe_foreign_close_topology_distinguishes_item_and_close_slots() {
    for (open, end, effect, owner, foreign, delimiter) in [
        (
            "(",
            ")",
            false,
            SyntaxKind::ParenthesizedTypeGroup,
            "]",
            Delimiter::Bracket,
        ),
        (
            "'[",
            "]",
            true,
            SyntaxKind::EffectRowType,
            ")",
            Delimiter::Parenthesis,
        ),
    ] {
        for (parts, gap) in [
            (vec!["@"], " "),
            (vec![foreign], " "),
            (vec![foreign, foreign], " "),
            (vec![foreign, foreign], ""),
            (vec!["@", foreign], " "),
            (vec![foreign, "@"], " "),
        ] {
            let source = format!("{open} {}/*é*/A{end}", parts.join(gap));
            for origin in [0, 40] {
                let mut at = open.len() + 1;
                let mut expected = Vec::new();
                let mut slots = Vec::new();
                for (id, part) in parts.iter().enumerate() {
                    let range = origin + at..origin + at + part.len();
                    let kind = if *part == foreign {
                        expected.push(close(
                            id as u32,
                            effect,
                            range,
                            Some(UnexpectedCategory::Punctuation(PunctuationEvidence::Close(
                                delimiter,
                            ))),
                        ));
                        SyntaxKind::TypeDelimitedForeignClose
                    } else {
                        expected.push(item(id as u32, effect, range, true));
                        SyntaxKind::Error
                    };
                    slots.push((kind, at..at + part.len(), *part));
                    at += part.len() + gap.len();
                }
                let root = assert_complete_type_recovery(&source, origin, &expected);
                let parent = root
                    .descendants()
                    .find(|node| node.kind() == owner)
                    .unwrap();
                assert_eq!(parent.to_string(), source);
                let base = usize::from(parent.text_range().start());
                let actual: Vec<_> = parent
                    .children_with_tokens()
                    .filter(|child| {
                        matches!(
                            child.kind(),
                            SyntaxKind::Error | SyntaxKind::TypeDelimitedForeignClose
                        )
                    })
                    .collect();
                assert_eq!(actual.len(), slots.len());
                for (child, (kind, range, text)) in actual.iter().zip(slots) {
                    assert_eq!(child.kind(), kind);
                    assert_eq!(child.to_string(), text);
                    assert_eq!(usize::from(child.text_range().start()), base + range.start);
                    assert_eq!(usize::from(child.text_range().end()), base + range.end);
                    if kind == SyntaxKind::TypeDelimitedForeignClose {
                        let wrapper = child.as_node().unwrap();
                        assert_eq!(wrapper.parent().unwrap(), parent);
                        let leaves: Vec<_> = wrapper.children_with_tokens().collect();
                        assert!(!leaves.is_empty());
                        assert!(
                            leaves.iter().all(|leaf| leaf.as_token().is_some()
                                && leaf.kind() == SyntaxKind::Error)
                        );
                        assert_eq!(
                            leaves.first().unwrap().text_range().start(),
                            wrapper.text_range().start()
                        );
                        assert_eq!(
                            leaves.last().unwrap().text_range().end(),
                            wrapper.text_range().end()
                        );
                    }
                }
                assert!(
                    parent
                        .children_with_tokens()
                        .any(|child| child.kind() == SyntaxKind::BlockComment
                            && child.to_string() == "/*é*/")
                );
            }
        }
    }
}

#[test]
fn pe_foreign_close_topology_excludes_accepted_and_other_delimited_owners() {
    for source in ["()", "(A)", "'[]", "'[A]", "T(A)", "G T[F A]->U"] {
        let root = assert_complete_type_recovery(source, 0, &[]);
        assert!(
            !root
                .descendants()
                .any(|node| node.kind() == SyntaxKind::TypeDelimitedForeignClose)
        );
    }
    for (source, expected, error_parent) in [
        (
            "T(A])",
            expected_type_call_close_error(0, 3..4),
            SyntaxKind::TypeCallClose,
        ),
        (
            "T [A)] -> U",
            bracket_recovery::close(0, 4..5, Some(Delimiter::Parenthesis)),
            SyntaxKind::BracketRow,
        ),
    ] {
        let root = assert_complete_type_recovery(source, 0, &[expected]);
        assert_foreign_close_count(&root, 0);
        let errors = recovery_groups(&root);
        assert_eq!(errors.len(), 1);
        assert_eq!(errors[0].parent().unwrap().kind(), error_parent);
    }
}

fn assert_foreign_close_count(root: &crate::SyntaxNode, expected: usize) {
    assert_eq!(
        root.descendants()
            .filter(|node| node.kind() == SyntaxKind::TypeDelimitedForeignClose)
            .count(),
        expected
    );
}

#[test]
fn pe_item_slots_publish_missing_and_error_with_retry_leading_outside_error() {
    for (source, effect, at) in [("(,)", false, 1), ("'[,]", true, 2)] {
        assert_complete_type_recovery(source, 0, &[item(0, effect, at..at, false)]);
    }
    for (source, effect, range, text) in [
        ("(@ A)", false, 1..2, "@"),
        ("'[@ A]", true, 2..3, "@"),
        ("(@ . A)", false, 1..4, "@ ."),
        ("(A @ B)", false, 3..4, "@"),
        ("'[@/*é*/A]", true, 2..3, "@"),
        ("(@\r\n  A)", false, 1..2, "@"),
        ("'[@\n  A]", true, 2..3, "@"),
    ] {
        let root = assert_complete_type_recovery(source, 0, &[item(0, effect, range, true)]);
        let error = recovery_groups(&root).into_iter().next().unwrap();
        assert_eq!(error.text(), text, "{source:?}");
        assert_eq!(
            error.parent().unwrap().kind(),
            if effect {
                SyntaxKind::EffectRowType
            } else {
                SyntaxKind::ParenthesizedTypeGroup
            }
        );
        assert!(error.next_sibling_or_token().is_some_and(|child| matches!(
            child.kind(),
            SyntaxKind::Whitespace | SyntaxKind::BlockComment | SyntaxKind::Newline
        )));
    }
}

#[test]
fn pe_closes_recover_unclaimed_tokens_and_preserve_actual_matching_closes() {
    for (source, effect, at, actual, missing) in [
        ("(])", false, 1, Delimiter::Bracket, None),
        ("(]", false, 1, Delimiter::Bracket, Some(2)),
        ("'[)]", true, 2, Delimiter::Parenthesis, None),
        ("'[)", true, 2, Delimiter::Parenthesis, Some(3)),
    ] {
        let mut expected = vec![close(
            0,
            effect,
            at..at + 1,
            Some(UnexpectedCategory::Punctuation(PunctuationEvidence::Close(
                actual,
            ))),
        )];
        if let Some(at) = missing {
            expected.push(close(1, effect, at..at, None));
        }
        let root = assert_complete_type_recovery(source, 0, &expected);
        assert_foreign_close_count(&root, 1);
        let error = recovery_groups(&root).into_iter().next().unwrap();
        assert_eq!(
            error.first_token().unwrap().text(),
            if actual == Delimiter::Bracket {
                "]"
            } else {
                ")"
            }
        );
        assert_eq!(error.first_token().unwrap().kind(), SyntaxKind::Error);
    }
    for (source, effect, at) in [("(A", false, 2), ("'[A", true, 3)] {
        let root = assert_complete_type_recovery(source, 0, &[close(0, effect, at..at, None)]);
        assert_foreign_close_count(&root, 0);
    }
    let root = assert_complete_type_recovery(
        "T((A] )",
        0,
        &[
            close(
                0,
                false,
                4..5,
                Some(UnexpectedCategory::Punctuation(PunctuationEvidence::Close(
                    Delimiter::Bracket,
                ))),
            ),
            expected_type_call_close(1, 7),
        ],
    );
    assert_foreign_close_count(&root, 1);
}

#[test]
fn pe_close_errors_resume_with_owner_trivia_and_protected_caller_words() {
    for (prefix, effect, actual) in [
        ("(]", false, Delimiter::Bracket),
        ("'[)", true, Delimiter::Parenthesis),
    ] {
        let at = prefix.len() - 1;
        let error = close(
            0,
            effect,
            at..at + 1,
            Some(UnexpectedCategory::Punctuation(PunctuationEvidence::Close(
                actual,
            ))),
        );
        for gap in [" ", "/*é*/", "\r\n  "] {
            let source = format!("{prefix}{gap}A{}", if effect { "]" } else { ")" });
            let root = assert_complete_type_recovery(&source, 0, std::slice::from_ref(&error));
            assert_foreign_close_count(&root, 1);
            let node = recovery_groups(&root).into_iter().next().unwrap();
            let wrapper = node.parent().unwrap();
            assert_eq!(wrapper.kind(), SyntaxKind::TypeDelimitedForeignClose);
            let mut following = wrapper.next_sibling_or_token();
            let mut leading = String::new();
            while let Some(element) = following {
                if element.kind() == SyntaxKind::TypeExpression {
                    assert_eq!(element.to_string(), "A");
                    break;
                }
                leading.push_str(&element.to_string());
                following = element.next_sibling_or_token();
            }
            assert_eq!(leading, gap);
        }
        let source = format!("{prefix} else rest");
        let expected = [error, close(1, effect, prefix.len()..prefix.len(), None)];
        let frozen = frozen_recovery_ids(&expected);
        for (input, records) in [
            (None, expected.as_slice()),
            (Some(frozen.as_slice()), frozen.as_slice()),
        ] {
            let run = run_contextual_type_snapshot(
                &source,
                crate::type_expr::TypeMlContext::INACTIVE,
                crate::lexical::stops::STOP_ELSE,
                0,
                0,
                LineEntry::InLine,
                None,
                input,
            );
            assert_eq!(run.green.to_string(), format!("sentinel{prefix}"));
            assert_foreign_close_count(&crate::SyntaxNode::new_root(run.green.clone()), 1);
            assert_eq!(run.records, records);
            assert_eq!(run.slots, records.len());
            assert_eq!(run.remainder, " rest");
            let NormalizedExit::Complete(Err(Either::Left(mut pending)), LineEntry::InLine) =
                run.exit
            else {
                panic!("post-close-error caller word must remain pending")
            };
            assert_eq!(pending.payload_view().spelling(), Some("else"));
            assert_eq!(emit_pending_leading_text(&mut pending), " ");
        }
    }
}

#[test]
fn pe_error_runs_keep_abstract_fence_items_unconsumed() {
    let fence = FenceBoundary {
        opener: FenceOpener {
            line: 0,
            marker: 0..3,
            marker_width: 3,
        },
        prefix_policy: FencePrefixPolicy::ActivePrefixQuote { depth: 2, base: 0 },
        close_column: 0,
    };
    for (prefix, effect, error) in [
        ("> > (@", false, item(0, false, 5..6, true)),
        ("> > '[@", true, item(0, true, 6..7, true)),
        (
            "> > (]",
            false,
            close(
                0,
                false,
                5..6,
                Some(UnexpectedCategory::Punctuation(PunctuationEvidence::Close(
                    Delimiter::Bracket,
                ))),
            ),
        ),
        (
            "> > '[)",
            true,
            close(
                0,
                true,
                6..7,
                Some(UnexpectedCategory::Punctuation(PunctuationEvidence::Close(
                    Delimiter::Parenthesis,
                ))),
            ),
        ),
    ] {
        let source = format!("{prefix}\n> > ```\nouter");
        // P retains its earlier remaining-start anchor; E uses the inspected
        // abstract boundary, at the next physical line after this LF.
        let close_at = prefix.len() + usize::from(effect);
        let expected = [error, close(1, effect, close_at..close_at, None)];
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
            assert_foreign_close_count(
                &crate::SyntaxNode::new_root(green.clone()),
                usize::from(!prefix.ends_with('@')),
            );
            assert_eq!(actual, records);
            assert_eq!(remainder, "> > ```\nouter");
            let Some(NormalizedExit::Complete(
                Err(Either::Left(pending)),
                LineEntry::PhysicalStart,
            )) = exit
            else {
                panic!("Error must preserve abstract fence boundary")
            };
            assert!(pending.payload_view().is_boundary());
            // Abstract boundary Items deliberately prohibit the raw-item emit
            // helper; inspect the retained newline without mutating it.
            assert!(pending.leading_view().has_ordinary_newline());
            assert_eq!(pending.leading_view().remaining_physical_parts(), 1);
        }
    }
}

#[test]
fn effect_separators_react_only_to_outer_typeapply_provenance() {
    for (source, at) in [
        ("'[A{}]", 3),
        ("G '[F A]", 6),
        ("G '[F\n  A]", 8),
        ("G '[F\r\n  A]", 9),
        ("G ('[F A])", 7),
        ("G T('[F A])", 8),
        ("G T['[F A]]->U", 8),
    ] {
        let root = assert_complete_type_recovery(source, 0, &[separator(0, true, at)]);
        let effect = root
            .descendants()
            .find(|node| node.kind() == SyntaxKind::EffectRowType)
            .unwrap();
        assert_eq!(
            effect
                .children()
                .filter(|node| node.kind() == SyntaxKind::TypeExpression)
                .count(),
            2
        );
        assert!(
            effect
                .children_with_tokens()
                .any(|child| child.kind() == SyntaxKind::RBracket)
        );
    }
    for source in [
        "'[F A]",
        "G '[F , A]",
        "G '[F\nA]",
        "G '[F\n  ]",
        ":{Tag '[F A]}",
    ] {
        assert_complete_type_recovery(source, 0, &[]);
    }
    assert_complete_type_recovery("(A{})", 0, &[separator(0, false, 2)]);
}

#[test]
fn pe_records_nest_inside_reserved_pv_errors_and_keep_native_pv_close() {
    for (source, expected) in [
        (
            ":{'[F}",
            vec![
                expected_type_error(0, TypeRole::PolymorphicVariantTagName, 2..5),
                close(1, true, 5..5, None),
            ],
        ),
        (
            ":{(@ A)}",
            vec![
                expected_type_error(0, TypeRole::PolymorphicVariantTagName, 2..7),
                item(1, false, 3..4, true),
            ],
        ),
    ] {
        let root = assert_complete_type_recovery(source, 0, &expected);
        assert_foreign_close_count(&root, 0);
        let pv = root
            .descendants()
            .find(|node| node.kind() == SyntaxKind::PolymorphicVariantType)
            .unwrap();
        assert!(
            pv.children_with_tokens()
                .any(|child| child.kind() == SyntaxKind::RBrace)
        );
        let outer_error = recovery_groups(&pv).into_iter().next().unwrap();
        assert!(
            outer_error
                .descendants_with_tokens()
                .skip(1)
                .any(|node| matches!(
                    node.kind(),
                    SyntaxKind::Error | SyntaxKind::Invalid | SyntaxKind::Missing
                ))
        );
    }
}

#[test]
fn pe_error_handoff_preserves_caller_item_and_shifted_frozen_records() {
    use crate::type_expr::TypeMlContext;
    for (source, effect, at) in [("(@ : rest", false, 1), ("'[@ : rest", true, 2)] {
        let expected = [
            item(0, effect, at..at + 1, true),
            close(1, effect, at + 1..at + 1, None),
        ];
        let frozen = frozen_recovery_ids(&expected);
        for (input, records) in [
            (None, expected.as_slice()),
            (Some(frozen.as_slice()), frozen.as_slice()),
        ] {
            let run = run_contextual_type_snapshot(
                source,
                TypeMlContext::INACTIVE,
                STOP_COLON,
                0,
                0,
                LineEntry::InLine,
                None,
                input,
            );
            assert_eq!(run.records, records);
            assert_foreign_close_count(&crate::SyntaxNode::new_root(run.green.clone()), 0);
            assert_eq!(
                run.green.to_string(),
                format!("sentinel{}", &source[..at + 1])
            );
            assert_eq!(run.remainder, " rest");
            let NormalizedExit::Complete(Err(Either::Left(mut pending)), _) = run.exit else {
                panic!("caller must keep colon")
            };
            assert_eq!(pending.payload_view().spelling(), Some(":"));
            assert_eq!(emit_pending_leading_text(&mut pending), " ");
        }
    }
    assert_complete_type_recovery("'[@ A]", 40, &[item(0, true, 42..43, true)]);
    assert_complete_type_recovery("G '[F A]", 40, &[separator(0, true, 46)]);
}
