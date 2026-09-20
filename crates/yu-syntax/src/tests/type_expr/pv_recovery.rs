use crate::tests::type_expr::*;

fn expected_record(range: Range<usize>, error: bool) -> ExpectedStructural {
    (
        if error {
            StructuralKind::ErrorGroup
        } else {
            StructuralKind::Missing
        },
        range,
    )
}

fn missing_tag(_: u32, at: usize) -> ExpectedStructural {
    expected_record(at..at, false)
}

fn missing_close(_: u32, at: usize) -> ExpectedStructural {
    expected_record(at..at, false)
}

fn payload_error(id: u32, range: Range<usize>) -> ExpectedStructural {
    let _ = id;
    expected_record(range, true)
}

fn assert_complete(source: &str, expected: &[ExpectedStructural]) -> SyntaxNode {
    let (green, exit, accepted, remainder, facts) =
        run_required_type_with_structural_diagnostics(source, 0, LineEntry::InLine, None);
    assert!(accepted, "{source:?}");
    assert_eq!(green.to_string(), source, "{source:?}");
    assert_eq!(facts, expected, "{source:?}");
    assert!(
        matches!(exit, NormalizedExit::Complete(Err(Either::Right(_)), _)),
        "{source:?}"
    );
    assert_eq!(remainder, "");
    SyntaxNode::new_root(green)
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
    for (source, range, close_at) in [
        (":{;A}", 2..3, None),
        (":{A ; B}", 4..5, None),
        (":{]}", 2..3, None),
        (":{)", 2..3, Some(3)),
    ] {
        let mut records = vec![expected_record(range, true)];
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
        (":{;}", expected_record(2..3, true)),
        (":{]}", expected_record(2..3, true)),
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

fn direct_kind_text(node: &SyntaxNode) -> Vec<(SyntaxKind, String)> {
    node.children_with_tokens()
        .map(|child| (child.kind(), child.to_string()))
        .collect()
}

fn pv_cst(source: &str) -> SyntaxNode {
    let (green, _) = run_type(source);
    let root = SyntaxNode::new_root(green);
    assert_eq!(root.text(), source, "{source:?}");
    root
}

fn direct_pv(root: &SyntaxNode) -> SyntaxNode {
    root.descendants()
        .find(|node| node.kind() == SyntaxKind::PolymorphicVariantType)
        .expect("polymorphic variant type")
}

#[test]
fn pv_semantic_missing_slots_use_direct_ordered_siblings() {
    use SyntaxKind::{
        Colon, Comma, LBrace, Missing, Newline, PolymorphicVariantTag as Tag, RBrace, Whitespace,
    };

    // Direct sibling order distinguishes the repeated/unfilled Tag vacancy
    // from the terminal Close vacancy, including equal-offset EOF cases.
    for (source, expected) in [
        (
            ":{,,A}",
            vec![Colon, LBrace, Missing, Comma, Missing, Comma, Tag, RBrace],
        ),
        (":{,}", vec![Colon, LBrace, Missing, Comma, RBrace]),
        (":{A,}", vec![Colon, LBrace, Tag, Comma, RBrace]),
        (":{A,", vec![Colon, LBrace, Tag, Comma, Missing, Missing]),
        (":{A\n", vec![Colon, LBrace, Tag, Newline, Missing, Missing]),
        (":{", vec![Colon, LBrace, Missing]),
    ] {
        let root = pv_cst(source);
        let variant = direct_pv(&root);
        let children = variant.children_with_tokens().collect::<Vec<_>>();
        assert_eq!(
            children
                .iter()
                .map(|child| child.kind())
                .collect::<Vec<_>>(),
            expected,
            "{source:?}"
        );
        if source == ":{A," || source == ":{A\n" {
            let missing = children
                .iter()
                .filter(|child| child.kind() == Missing)
                .collect::<Vec<_>>();
            assert_eq!(missing.len(), 2);
            assert_eq!(missing[0].text_range(), missing[1].text_range());
            assert_eq!(
                children.iter().position(|child| child.kind() == Missing),
                Some(children.len() - 2),
                "the unfilled Tag precedes the final Close"
            );
        }
    }

    let root = pv_cst(":{A\r\n");
    assert_eq!(
        direct_kind_text(&direct_pv(&root)),
        vec![
            (Colon, ":".into()),
            (LBrace, "{".into()),
            (Tag, "A".into()),
            (Newline, "\r\n".into()),
            (Missing, "".into()),
            (Missing, "".into()),
        ]
    );

    let root = pv_cst(":{:{A");
    let missing = root
        .descendants()
        .filter(|node| node.kind() == Missing)
        .collect::<Vec<_>>();
    assert_eq!(missing.len(), 2);
    assert_eq!(missing[0].text_range(), missing[1].text_range());
    assert_eq!(
        missing
            .iter()
            .map(|node| {
                node.ancestors()
                    .filter(|ancestor| ancestor.kind() == SyntaxKind::PolymorphicVariantType)
                    .count()
            })
            .collect::<Vec<_>>(),
        [2, 1],
        "nested and outer Close occurrences use ancestry/order, not range identity"
    );

    let root = pv_cst(":{ A}");
    assert_eq!(
        direct_pv(&root)
            .children_with_tokens()
            .next()
            .unwrap()
            .kind(),
        Colon
    );
    assert!(
        direct_pv(&root)
            .children_with_tokens()
            .any(|child| child.kind() == Whitespace)
    );
}

#[test]
fn pv_semantic_error_slots_use_direct_groups_and_ancestry() {
    use SyntaxKind::{
        Error, Invalid, PolymorphicVariantForeignClose as ForeignClose,
        PolymorphicVariantPayload as Payload, PolymorphicVariantTag as Tag, TypeExpression,
    };

    // A direct maximal raw group is Separator-owned. ForeignClose makes Close
    // structural without consulting Error spelling or temporary records.
    let root = pv_cst(":{ /*é*/;;])];;}");
    let variant = direct_pv(&root);
    let direct = variant.children_with_tokens().collect::<Vec<_>>();
    assert_eq!(
        direct.iter().map(|child| child.kind()).collect::<Vec<_>>(),
        vec![
            SyntaxKind::Colon,
            SyntaxKind::LBrace,
            SyntaxKind::Whitespace,
            SyntaxKind::BlockComment,
            Error,
            Error,
            ForeignClose,
            ForeignClose,
            ForeignClose,
            Error,
            Error,
            SyntaxKind::RBrace,
        ]
    );
    assert!(direct.iter().any(|child| {
        child.kind() == SyntaxKind::BlockComment && child.to_string() == "/*é*/"
    }));
    let foreign = variant
        .children()
        .filter(|node| node.kind() == ForeignClose)
        .collect::<Vec<_>>();
    assert_eq!(foreign.len(), 3);
    for close in foreign {
        assert_eq!(close.parent(), Some(variant.clone()));
        assert!(
            close
                .children_with_tokens()
                .all(|child| child.kind() == Error && child.as_token().is_some())
        );
    }

    let root = pv_cst(":{A@Int}");
    let variant = direct_pv(&root);
    let tags = variant
        .children()
        .filter(|node| node.kind() == Tag)
        .collect::<Vec<_>>();
    assert_eq!(tags.len(), 2);
    assert_eq!(tags[0].text(), "A");
    assert!(
        tags[1]
            .children_with_tokens()
            .map(|child| child.kind())
            .eq([Error, SyntaxKind::Identifier])
    );
    assert!(!tags[1].descendants().any(|node| node.kind() == Invalid));

    let root = pv_cst(":{123::T}");
    let tag = direct_pv(&root)
        .children()
        .find(|node| node.kind() == Tag)
        .unwrap();
    let tag_children = tag.children_with_tokens().collect::<Vec<_>>();
    assert_eq!(
        tag_children
            .iter()
            .map(|child| child.kind())
            .collect::<Vec<_>>(),
        [Invalid]
    );
    let invalid = tag_children[0].as_node().unwrap();
    assert!(
        invalid
            .children()
            .next()
            .is_some_and(|node| node.kind() == TypeExpression)
    );

    let root = pv_cst(":{A(Int)}");
    let variant = direct_pv(&root);
    let tag = variant.children().find(|node| node.kind() == Tag).unwrap();
    let tag_children = tag.children_with_tokens().collect::<Vec<_>>();
    let payload = tag_children
        .iter()
        .position(|child| child.kind() == Payload)
        .unwrap();
    let payload = tag_children[payload].as_node().unwrap();
    assert_eq!(payload.parent(), Some(tag));
    assert_eq!(
        payload
            .children_with_tokens()
            .map(|child| child.kind())
            .collect::<Vec<_>>(),
        [SyntaxKind::Missing, TypeExpression]
    );

    let root = pv_cst(":{A @/*é*/Int}");
    let payload = direct_pv(&root)
        .descendants()
        .find(|node| node.kind() == Payload)
        .unwrap();
    let children = payload.children_with_tokens().collect::<Vec<_>>();
    let error = children
        .iter()
        .position(|child| child.kind() == Error)
        .unwrap();
    let retry = children
        .iter()
        .position(|child| child.kind() == TypeExpression)
        .unwrap();
    assert!(error < retry, "the Payload Error precedes its retry Type");
    assert!(
        children[error + 1..retry]
            .iter()
            .any(|child| child.kind() == SyntaxKind::BlockComment && child.to_string() == "/*é*/")
    );
}

#[test]
fn pv_foreign_close_slots_preserve_positions_leading_and_type_tails() {
    for (prefix, mut records) in [
        (":{", vec![]),
        (":{A", vec![]),
        (":{A,", vec![]),
        (":{,", vec![missing_tag(0, 2)]),
    ] {
        for close in [")", "]"] {
            for leading in ["", " /*é*/", "\r\n"] {
                let start = prefix.len() + leading.len();
                let record = expected_record(start..start + 1, true);
                records.push(record);
                let source = format!("{prefix}{leading}{close}}}::Next");
                let root = assert_complete(&source, &records);
                assert_foreign_closes(&root, &[start..start + 1]);
                records.pop();
            }
        }
    }
    let root = assert_complete(":{)", &[expected_record(2..3, true), missing_close(1, 3)]);
    assert_foreign_closes(&root, &[2..3]);
}

#[test]
fn pv_mixed_repeated_foreign_closes_keep_separator_groups_direct() {
    let source = ":{;;])];;}";
    let expected = vec![
        (StructuralKind::ErrorGroup, 2..4),
        (StructuralKind::ErrorGroup, 4..5),
        (StructuralKind::ErrorGroup, 5..6),
        (StructuralKind::ErrorGroup, 6..7),
        (StructuralKind::ErrorGroup, 7..9),
    ];
    let (green, exit, accepted, remainder, actual) =
        run_required_type_with_structural_diagnostics(source, 0, LineEntry::InLine, None);
    assert!(accepted);
    assert!(matches!(
        exit,
        NormalizedExit::Complete(Err(Either::Right(_)), _)
    ));
    assert_eq!(remainder, "");
    assert_eq!(green.to_string(), source);
    assert_eq!(actual, expected);
    let root = SyntaxNode::new_root(green);
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
}

#[test]
fn pv_payload_recovery_keeps_gap_error_and_retry_at_the_payload_owner() {
    let boundary = expected_record(3..3, false);
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
        let root = assert_complete(source, &[(StructuralKind::ErrorGroup, 3..4)]);
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
            let root = assert_complete(&source, &[(StructuralKind::Invalid, 2..end)]);
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
            (StructuralKind::Invalid, 2..5),
            missing_close(1, 5),
            missing_close(2, 5),
        ],
    );
}

#[test]
fn pv_malformed_run_returns_complete_caller_item_before_retry() {
    use crate::type_expr::TypeMlContext;
    for (prefix, error_start, error_end, owner) in [
        (":{@", 2, 3, SyntaxKind::PolymorphicVariantType),
        (":{A @", 4, 5, SyntaxKind::PolymorphicVariantPayload),
        (":{]", 2, 3, SyntaxKind::PolymorphicVariantForeignClose),
    ] {
        for (stop, stops) in [(":", STOP_COLON), ("else", STOP_ELSE)] {
            // Owner dispatch admits `else` as a tag name after a foreign close.
            if owner == SyntaxKind::PolymorphicVariantForeignClose && stop == "else" {
                continue;
            }
            let source = format!("{prefix} {stop} rest");
            let error = if owner == SyntaxKind::PolymorphicVariantType {
                (StructuralKind::ErrorGroup, error_start..error_end)
            } else if owner == SyntaxKind::PolymorphicVariantPayload {
                payload_error(0, error_start..error_end)
            } else {
                expected_record(error_start..error_end, true)
            };
            let expected = [error, missing_close(1, error_end)];
            let run = run_contextual_type_snapshot(
                &source,
                TypeMlContext::INACTIVE,
                stops,
                0,
                0,
                LineEntry::InLine,
                None,
            );
            assert_eq!(run.green.to_string(), format!("sentinel{prefix}"));
            let expected = expected.map(|(kind, range)| {
                (
                    kind,
                    "sentinel".len() + range.start.."sentinel".len() + range.end,
                )
            });
            assert_eq!(run.facts, expected);
            assert_foreign_closes(
                &SyntaxNode::new_root(run.green.clone()),
                if prefix == ":{]" { &[10..11] } else { &[] },
            );
            assert_eq!(run.remainder, " rest");
            assert_eq!(run.successor_origin, prefix.len() + 1 + stop.len());
            let NormalizedExit::Complete(Err(Either::Left(mut pending)), _) = run.exit else {
                panic!("caller stop must remain pending")
            };
            assert_eq!(pending.payload_view().spelling(), Some(stop));
            assert_eq!(emit_pending_leading_text(&mut pending), " ");
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
            [payload_error(0, 8..9), missing_close(1, 9)],
            "> > :{A @",
            vec![],
        ),
        (
            "> > :{]\n> > ```\nouter\n",
            [expected_record(6..7, true), missing_close(1, 7)],
            "> > :{]",
            vec![6..7],
        ),
    ] {
        let (green, exit, remainder, facts) = run_type_normalized_with_structural_diagnostics(
            source,
            0,
            LineEntry::PhysicalStart,
            Some(&fence),
        );
        assert_eq!(green.to_string(), text);
        assert_foreign_closes(&SyntaxNode::new_root(green.clone()), &ranges);
        assert_eq!(facts, expected);
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
        let root = assert_complete(source, &[]);
        assert_foreign_closes(&root, &[]);
    }
}
