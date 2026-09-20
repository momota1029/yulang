use crate::tests::type_expr::bracket_arrow_recovery::arrow;
use crate::tests::type_expr::*;

fn structural_fact(range: Range<usize>, error: bool) -> ExpectedStructural {
    (
        if error {
            StructuralKind::ErrorGroup
        } else {
            StructuralKind::Missing
        },
        range,
    )
}

pub(super) fn close(_: u32, range: Range<usize>, actual: Option<Delimiter>) -> ExpectedStructural {
    structural_fact(range, actual.is_some())
}

fn item(_: u32, range: Range<usize>, error: bool) -> ExpectedStructural {
    structural_fact(range, error)
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
fn bracket_row_item_and_close_roles_collide_in_direct_cst_topology() {
    use SyntaxKind::*;

    // The approved Item retry and close-only retry remain distinct through
    // their direct CST topology, not a parser-side recovery side channel.
    let cases = [
        ("T [A@] -> U", item(0, 4..5, true)),
        ("T [A)] -> U", close(0, 4..5, Some(Delimiter::Parenthesis))),
    ];
    let mut topologies = Vec::new();
    for (source, expected) in cases {
        let root = assert_complete_type_recovery(source, 0, &[expected.clone()]);
        let shift = "sentinel".len();
        assert_eq!(root.to_string(), format!("sentinel{source}"));
        let relative = |range: rowan::TextRange| {
            usize::from(range.start()) - shift..usize::from(range.end()) - shift
        };
        let row = root
            .descendants()
            .find(|node| node.kind() == BracketRow)
            .unwrap();
        assert_eq!(relative(row.text_range()), 2..6);
        assert_eq!(
            row.text_range(),
            rowan::TextRange::new((shift as u32 + 2).into(), (shift as u32 + 6).into())
        );
        let topology = row
            .descendants_with_tokens()
            .map(|element| {
                (
                    element.kind(),
                    element.parent().map(|parent| parent.kind()),
                    relative(element.text_range()),
                )
            })
            .collect::<Vec<_>>();
        assert_eq!(
            topology,
            vec![
                (BracketRow, Some(TypeArrowTail), 2..6),
                (LBracket, Some(BracketRow), 2..3),
                (TypeExpression, Some(BracketRow), 3..4),
                (Identifier, Some(TypeExpression), 3..4),
                (Error, Some(BracketRow), 4..5),
                (RBracket, Some(BracketRow), 5..6),
            ]
        );
        assert!(
            !row.descendants()
                .any(|node| matches!(node.kind(), Missing | Invalid))
        );
        let groups = recovery_groups(&row);
        assert_eq!(groups.len(), 1);
        assert_eq!(groups[0].parent(), Some(row.clone()));
        assert_eq!(relative(groups[0].text_range()), 4..5);
        let tail = row.parent().unwrap();
        assert_eq!(tail.kind(), TypeArrowTail);
        assert_eq!(tail.parent().unwrap().kind(), TypeExpression);
        assert_eq!(relative(tail.text_range()), 2..source.len());
        assert_eq!(
            tail.children_with_tokens()
                .skip(1)
                .map(|element| (
                    element.kind(),
                    element.to_string(),
                    relative(element.text_range())
                ))
                .collect::<Vec<_>>(),
            vec![
                (Whitespace, " ".into(), 6..7),
                (Arrow, "->".into(), 7..9),
                (TypeExpression, " U".into(), 9..11),
            ]
        );
        topologies.push(topology);
    }
    assert_eq!(topologies[0], topologies[1]);
}

#[test]
fn bracket_row_no_gap_separator_missing_is_selected_by_direct_item_order() {
    use SyntaxKind::*;

    let source = "T [A{}] -> U";
    let run = run_contextual_type_snapshot(
        source,
        crate::type_expr::TypeMlContext::INACTIVE,
        0,
        0,
        0,
        LineEntry::InLine,
        None,
    );
    let root = SyntaxNode::new_root(run.green.clone());
    let shift = "sentinel".len();
    let relative = |range: rowan::TextRange| {
        usize::from(range.start()) - shift..usize::from(range.end()) - shift
    };
    assert_eq!(root.to_string(), format!("sentinel{source}"));
    let row = root
        .descendants()
        .find(|node| node.kind() == BracketRow)
        .unwrap();
    assert_eq!(
        row.descendants_with_tokens()
            .map(|element| (
                element.kind(),
                element.parent().map(|parent| parent.kind()),
                element.to_string(),
                relative(element.text_range()),
            ))
            .collect::<Vec<_>>(),
        vec![
            (BracketRow, Some(TypeArrowTail), "[A{}]".into(), 2..7),
            (LBracket, Some(BracketRow), "[".into(), 2..3),
            (TypeExpression, Some(BracketRow), "A".into(), 3..4),
            (Identifier, Some(TypeExpression), "A".into(), 3..4),
            (Missing, Some(BracketRow), "".into(), 4..4),
            (TypeExpression, Some(BracketRow), "{}".into(), 4..6),
            (NamedRecordType, Some(TypeExpression), "{}".into(), 4..6),
            (LBrace, Some(NamedRecordType), "{".into(), 4..5),
            (
                NamedRecordTypeClose,
                Some(NamedRecordType),
                "}".into(),
                5..6
            ),
            (RBrace, Some(NamedRecordTypeClose), "}".into(), 5..6),
            (RBracket, Some(BracketRow), "]".into(), 6..7),
        ]
    );
    let children = row.children_with_tokens().collect::<Vec<_>>();
    assert_eq!(
        children
            .iter()
            .map(|child| child.kind())
            .collect::<Vec<_>>(),
        vec![LBracket, TypeExpression, Missing, TypeExpression, RBracket]
    );
    let missing = children[2].as_node().unwrap();
    assert_eq!(missing.parent(), Some(row.clone()));
    assert_eq!(missing.children_with_tokens().count(), 0);
    assert_eq!(
        row.children().filter(|node| node.kind() == Missing).count(),
        1
    );
    assert_eq!(
        root.descendants()
            .filter(|node| node.kind() == Missing)
            .collect::<Vec<_>>(),
        vec![missing.clone()]
    );
    assert!(
        !root
            .descendants_with_tokens()
            .any(|element| matches!(element.kind(), Error | Invalid))
    );

    let tail = row.parent().unwrap();
    assert_eq!(tail.parent().unwrap().kind(), TypeExpression);
    assert_eq!(relative(tail.text_range()), 2..source.len());
    assert_eq!(
        tail.children_with_tokens()
            .skip(1)
            .flat_map(|element| {
                match element {
                    rowan::NodeOrToken::Node(node) => {
                        node.descendants_with_tokens().collect::<Vec<_>>()
                    }
                    token => vec![token],
                }
            })
            .map(|element| (
                element.kind(),
                element.parent().unwrap().kind(),
                element.to_string(),
                relative(element.text_range()),
            ))
            .collect::<Vec<_>>(),
        vec![
            (Whitespace, TypeArrowTail, " ".into(), 7..8),
            (Arrow, TypeArrowTail, "->".into(), 8..10),
            (TypeExpression, TypeArrowTail, " U".into(), 10..12),
            (Whitespace, TypeExpression, " ".into(), 10..11),
            (Identifier, TypeExpression, "U".into(), 11..12),
        ]
    );

    // Select this occurrence from the direct completed-item / Missing / item
    // order. This covers only the authoritative no-gap witness, not the
    // deeper-newline alternative.
    match (
        row.kind(),
        children[1].kind(),
        children[2].kind(),
        children[3].kind(),
    ) {
        (BracketRow, TypeExpression, Missing, TypeExpression) => {}
        identity => panic!("unexpected missing boundary identity: {identity:?}"),
    }
    let range = relative(missing.text_range());
    assert_eq!(range, 4..4);
    let expected = (StructuralKind::Missing, range);
    assert_eq!(run.facts, vec![(StructuralKind::Missing, 12..12)]);
    let reparsed = assert_complete_type_recovery(source, 0, &[expected]);
    assert_eq!(reparsed.green(), root.green());
}

#[test]
fn bracket_row_deeper_newline_separator_missing_follows_returned_pv_close() {
    use SyntaxKind::*;

    let source = "T [:{A\n  B] -> U";
    let run = run_contextual_type_snapshot(
        source,
        crate::type_expr::TypeMlContext::INACTIVE,
        0,
        0,
        0,
        LineEntry::InLine,
        None,
    );
    let root = SyntaxNode::new_root(run.green.clone());
    let shift = "sentinel".len();
    let relative = |range: rowan::TextRange| {
        usize::from(range.start()) - shift..usize::from(range.end()) - shift
    };
    assert_eq!(root.to_string(), format!("sentinel{source}"));
    let row = root
        .descendants()
        .find(|node| node.kind() == BracketRow)
        .unwrap();
    assert_eq!(
        row.descendants_with_tokens()
            .map(|element| (
                element.kind(),
                element.parent().map(|parent| parent.kind()),
                element.to_string(),
                relative(element.text_range()),
            ))
            .collect::<Vec<_>>(),
        vec![
            (BracketRow, Some(TypeArrowTail), "[:{A\n  B]".into(), 2..11),
            (LBracket, Some(BracketRow), "[".into(), 2..3),
            (TypeExpression, Some(BracketRow), ":{A".into(), 3..6),
            (
                PolymorphicVariantType,
                Some(TypeExpression),
                ":{A".into(),
                3..6
            ),
            (Colon, Some(PolymorphicVariantType), ":".into(), 3..4),
            (LBrace, Some(PolymorphicVariantType), "{".into(), 4..5),
            (
                PolymorphicVariantTag,
                Some(PolymorphicVariantType),
                "A".into(),
                5..6
            ),
            (Identifier, Some(PolymorphicVariantTag), "A".into(), 5..6),
            (Missing, Some(PolymorphicVariantType), "".into(), 6..6),
            (Newline, Some(BracketRow), "\n".into(), 6..7),
            (Whitespace, Some(BracketRow), "  ".into(), 7..9),
            (Missing, Some(BracketRow), "".into(), 9..9),
            (TypeExpression, Some(BracketRow), "B".into(), 9..10),
            (Identifier, Some(TypeExpression), "B".into(), 9..10),
            (RBracket, Some(BracketRow), "]".into(), 10..11),
        ]
    );
    assert!(
        !root
            .descendants_with_tokens()
            .any(|element| matches!(element.kind(), Error | Invalid))
    );
    let missing = root
        .descendants()
        .filter(|node| node.kind() == Missing)
        .collect::<Vec<_>>();
    assert_eq!(missing.len(), 2);
    assert!(
        missing
            .iter()
            .all(|node| node.children_with_tokens().count() == 0)
    );
    let children = row.children_with_tokens().collect::<Vec<_>>();
    assert_eq!(
        children
            .iter()
            .map(|child| child.kind())
            .collect::<Vec<_>>(),
        vec![
            LBracket,
            TypeExpression,
            Newline,
            Whitespace,
            Missing,
            TypeExpression,
            RBracket
        ]
    );
    assert_eq!(children[4].as_node(), Some(&missing[1]));
    let pv = missing[0].parent().unwrap();
    assert_eq!(pv.kind(), PolymorphicVariantType);
    assert_eq!(pv.last_child(), Some(missing[0].clone()));

    let tail = row.parent().unwrap();
    assert_eq!(tail.kind(), TypeArrowTail);
    assert_eq!(tail.parent().unwrap().kind(), TypeExpression);
    assert_eq!(relative(tail.text_range()), 2..source.len());
    assert_eq!(
        tail.children_with_tokens()
            .skip(1)
            .flat_map(|element| match element {
                rowan::NodeOrToken::Node(node) =>
                    node.descendants_with_tokens().collect::<Vec<_>>(),
                token => vec![token],
            })
            .map(|element| (
                element.kind(),
                element.parent().unwrap().kind(),
                element.to_string(),
                relative(element.text_range()),
            ))
            .collect::<Vec<_>>(),
        vec![
            (Whitespace, TypeArrowTail, " ".into(), 11..12),
            (Arrow, TypeArrowTail, "->".into(), 12..14),
            (TypeExpression, TypeArrowTail, " U".into(), 14..16),
            (Whitespace, TypeExpression, " ".into(), 14..15),
            (Identifier, TypeExpression, "U".into(), 15..16),
        ]
    );

    // Select preorder occurrences from the terminal PV slot and the row's
    // completed-item / native leading / Missing / item order.
    let expected = missing
        .iter()
        .map(|node| {
            let kind = match node.parent().unwrap().kind() {
                PolymorphicVariantType if pv.last_child().as_ref() == Some(node) => {
                    StructuralKind::Missing
                }
                BracketRow
                    if children[4].as_node() == Some(node)
                        && children[1].kind() == TypeExpression
                        && children[5].kind() == TypeExpression =>
                {
                    StructuralKind::Missing
                }
                owner => panic!("unexpected missing owner: {owner:?}"),
            };
            (kind, relative(node.text_range()))
        })
        .collect::<Vec<_>>();
    assert_eq!(
        expected
            .iter()
            .map(|(_, range)| range.clone())
            .collect::<Vec<_>>(),
        vec![6..6, 9..9]
    );
    assert_eq!(
        run.facts,
        expected
            .iter()
            .map(|(kind, range)| {
                (
                    *kind,
                    "sentinel".len() + range.start.."sentinel".len() + range.end,
                )
            })
            .collect::<Vec<_>>()
    );
    let reparsed = assert_complete_type_recovery(source, 0, &expected);
    assert_eq!(reparsed.green(), root.green());
}

#[test]
fn bracket_row_missing_and_local_close_slots_publish_in_source_order() {
    for (source, expected, row_missing) in [
        ("T [,] -> U", vec![item(0, 3..3, false)], 1),
        (
            "T [)] -> U",
            vec![
                item(0, 3..3, false),
                close(1, 3..4, Some(Delimiter::Parenthesis)),
            ],
            1,
        ),
        (
            "T [A)] -> U",
            vec![close(0, 4..5, Some(Delimiter::Parenthesis))],
            0,
        ),
        (
            "T [@ )] -> U",
            vec![
                item(0, 3..4, true),
                close(1, 5..6, Some(Delimiter::Parenthesis)),
            ],
            0,
        ),
        ("T [A))] -> U", vec![(StructuralKind::ErrorGroup, 4..6)], 0),
        (
            "T [",
            vec![
                item(0, 3..3, false),
                close(1, 3..3, None),
                arrow(2, 3..3, false),
            ],
            2,
        ),
        ("T [A", vec![close(0, 4..4, None), arrow(1, 4..4, false)], 1),
        (
            "T [@",
            vec![
                item(0, 3..4, true),
                close(1, 4..4, None),
                arrow(2, 4..4, false),
            ],
            1,
        ),
        (
            "T [A)",
            vec![
                close(0, 4..5, Some(Delimiter::Parenthesis)),
                close(1, 5..5, None),
                arrow(2, 5..5, false),
            ],
            1,
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
            row_missing
        );
        let groups = recovery_groups(&row);
        let mut expected_ranges: Vec<std::ops::Range<usize>> = Vec::new();
        for fact in expected
            .iter()
            .filter(|(kind, _)| *kind == StructuralKind::ErrorGroup)
        {
            let range = &fact.1;
            if let Some(last) = expected_ranges
                .last_mut()
                .filter(|last| last.end == range.start)
            {
                last.end = range.end;
            } else {
                expected_ranges.push(range.clone());
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
    assert_complete_type_recovery("T [A{}] -> U", 0, &[(StructuralKind::Missing, 4..4)]);
    let root =
        assert_complete_type_recovery("F(T [A)", 0, &[close(0, 6..6, None), arrow(1, 6..6, false)]);
    let native = root
        .descendants_with_tokens()
        .find(|child| child.kind() == SyntaxKind::RParen)
        .unwrap();
    assert_eq!(native.parent().unwrap().kind(), SyntaxKind::TypeCallClose);
    assert_eq!(
        native.parent().unwrap().parent().unwrap().kind(),
        SyntaxKind::TypeCallTail
    );
}

#[test]
fn bracket_row_close_retry_does_not_reenter_the_item_list() {
    for origin in [0, 40] {
        let expected = [
            close(0, origin + 4..origin + 5, Some(Delimiter::Parenthesis)),
            close(1, origin + 5..origin + 5, None),
            arrow(2, origin + 5..origin + 5, false),
        ];
        let run = run_contextual_type_snapshot(
            "T [A) B] -> U",
            crate::type_expr::TypeMlContext::INACTIVE,
            0,
            0,
            origin,
            LineEntry::InLine,
            None,
        );
        assert_eq!(run.green.to_string(), "sentinelT [A)");
        let expected = expected.map(|(kind, range)| {
            (
                kind,
                "sentinel".len() + range.start - origin.."sentinel".len() + range.end - origin,
            )
        });
        assert_eq!(run.facts, expected);
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
                let run = run_contextual_type_snapshot(
                    &source,
                    crate::type_expr::TypeMlContext::INACTIVE,
                    stops,
                    outer,
                    0,
                    LineEntry::InLine,
                    None,
                );
                assert_eq!(
                    run.green.to_string(),
                    format!("sentinel{prefix}"),
                    "{source:?}"
                );
                let raw_expected = expected
                    .iter()
                    .map(|(kind, range)| {
                        (
                            *kind,
                            "sentinel".len() + range.start.."sentinel".len() + range.end,
                        )
                    })
                    .collect::<Vec<_>>();
                assert_eq!(run.facts, raw_expected, "{source:?}");
                let NormalizedExit::Complete(Err(Either::Left(pending)), line) = run.exit else {
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
        close(1, 8..8, None),
        arrow(2, 8..8, false),
    ];
    let (green, exit, remainder, actual) = run_type_normalized_with_structural_diagnostics(
        "> > T [@\n> > ```\nouter",
        0,
        LineEntry::PhysicalStart,
        Some(&fence),
    );
    assert_eq!(green.to_string(), "> > T [@");
    assert_eq!(actual, expected);
    assert_eq!(remainder, "> > ```\nouter");
    let Some(NormalizedExit::Complete(Err(Either::Left(pending)), LineEntry::PhysicalStart)) = exit
    else {
        panic!("row preserves fence")
    };
    assert!(pending.payload_view().is_boundary());
    assert!(pending.leading_view().has_ordinary_newline());
    let root = assert_complete_type_recovery(
        ":{[e] (@ A)}",
        0,
        &[
            (StructuralKind::Invalid, 2..11),
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
        &[(StructuralKind::Invalid, 2..7), item(1, 3..4, true)],
    );
    let error = recovery_groups(&root).into_iter().next().unwrap();
    let crate::tests::recovery_output::RecoveryGroup::Structured(invalid) = error else {
        panic!("structured tag-name Invalid")
    };
    let groups = recovery_groups(&invalid);
    assert_eq!(groups.len(), 2);
    assert_eq!(groups[1].text(), "@");
}
