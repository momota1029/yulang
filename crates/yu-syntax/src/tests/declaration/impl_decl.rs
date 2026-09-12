use crate::tests::support::*;

#[test]
fn impl_schema_completed_type_statement_shell_composition() {
    use SyntaxKind::*;

    // Each product starts after a completed Head or completed Description.
    // The tuple fixes direct child kind, node/token identity and owned text;
    // cumulative UTF-8 widths fix every ordered byte range independently.
    let assert_shell = |source: &str,
                        expected: &[(SyntaxKind, bool, &str)],
                        pending_leading: &str,
                        pending_spelling: Option<&str>,
                        missing_count: usize,
                        error_count: usize| {
        let (green, exit) = run_statement(source);
        let root = SyntaxNode::new_root(green);
        let owned = expected.iter().map(|child| child.2).collect::<String>();
        let owned_end = owned.len() as u32;
        let assert_elements = |parent: &SyntaxNode, parts: &[(SyntaxKind, bool, &str)]| {
            let children = parent.children_with_tokens().collect::<Vec<_>>();
            assert_eq!(children.len(), parts.len(), "{source:?}: {parent:#?}");
            let mut start = u32::from(parent.text_range().start());
            for (child, (kind, is_node, text)) in children.iter().zip(parts) {
                let end = start + text.len() as u32;
                assert_eq!(child.parent(), Some(parent.clone()));
                assert_eq!(child.kind(), *kind, "{source:?}");
                assert_eq!(child.as_node().is_some(), *is_node);
                assert_eq!(child.to_string(), *text);
                assert_eq!(
                    child.text_range(),
                    rowan::TextRange::new(start.into(), end.into())
                );
                if *kind == Missing {
                    assert_eq!(child.as_node().unwrap().children_with_tokens().count(), 0);
                }
                start = end;
            }
            assert_eq!(parent.text_range().end(), start.into());
        };
        assert_eq!(root.kind(), Root);
        assert!(root.parent().is_none());
        let mut root_parts = vec![(Statement, true, owned.as_str())];
        // The ordinary harness emits pending EOF leading only after Statement.
        if pending_spelling.is_none() && !pending_leading.is_empty() {
            root_parts.push((Whitespace, false, pending_leading));
        }
        assert_elements(&root, &root_parts);
        let statement = root.first_child().expect("canonical Statement");
        assert_elements(&statement, &[(ImplDeclaration, true, owned.as_str())]);
        let implementation = statement.first_child().expect("ImplDeclaration");
        assert_elements(&implementation, expected);
        assert_eq!(implementation.to_string(), &source[..owned_end as usize]);
        for inline in implementation
            .children()
            .filter(|node| node.kind() == Statement && node.to_string().trim() == "x")
        {
            let chain = inline.first_child().expect("OperatorChain");
            assert_eq!(chain.kind(), OperatorChain);
            let identifier = chain.first_child().expect("IdentifierExpression");
            assert_eq!(identifier.kind(), IdentifierExpression);
            let text = inline.to_string();
            assert_elements(
                &identifier,
                &[
                    (Whitespace, false, &text[..text.len() - 1]),
                    (Identifier, false, "x"),
                ],
            );
            assert_eq!(identifier.parent(), Some(chain.clone()));
            assert_eq!(chain.parent(), Some(inline));
        }
        if let Some(description) = implementation
            .children()
            .find(|node| node.kind() == ImplDescription)
        {
            assert_elements(
                &description,
                &[
                    (Colon, false, ":"),
                    (Whitespace, false, " "),
                    (TypeExpression, true, "D"),
                ],
            );
        }
        for (kind, count) in [(Missing, missing_count), (Error, error_count), (Invalid, 0)] {
            assert_eq!(
                root.descendants_with_tokens()
                    .filter(|child| child.kind() == kind)
                    .count(),
                count,
                "{source:?}: {kind:?}"
            );
        }
        let mut ordinary_pending = match exit {
            Some(Err(Either::Right(end))) => end.item,
            Some(Err(Either::Left(item))) => item,
            _ => panic!("{source:?}: expected pending Item"),
        };
        assert_eq!(ordinary_pending.payload_view().spelling(), pending_spelling);
        assert_eq!(
            emit_pending_leading_text(&mut ordinary_pending),
            if pending_spelling.is_none() {
                ""
            } else {
                pending_leading
            }
        );

        // Normalized composition leaves the complete EOF/boundary Item pending.
        let (normalized, normalized_exit, remainder) =
            run_statement_normalized(source, 100, LineEntry::InLine, None);
        assert_eq!(remainder, "", "{source:?}");
        let normalized_root = SyntaxNode::new_root(normalized);
        assert_elements(&normalized_root, &[(Statement, true, owned.as_str())]);
        assert_eq!(
            normalized_root
                .first_child()
                .unwrap()
                .first_child()
                .unwrap()
                .green(),
            implementation.green()
        );
        let mut pending = pending_item(Some(normalized_exit), LineEntry::InLine);
        assert_eq!(pending.payload_view().spelling(), pending_spelling);
        assert_eq!(pending.payload_view().is_eof(), pending_spelling.is_none());
        assert_eq!(emit_pending_leading_text(&mut pending), pending_leading);
        implementation
    };

    for prefix in ["impl 型", "impl 型: D"] {
        let mut head = vec![
            (ImplKw, false, "impl"),
            (Whitespace, false, " "),
            (TypeExpression, true, "型"),
        ];
        if prefix.ends_with('D') {
            head.push((ImplDescription, true, ": D"));
        }
        for (tail, suffix, pending, missing, errors) in [
            (";", vec![(Semicolon, false, ";")], "", 0, 0),
            (
                " {}",
                vec![
                    (Whitespace, false, " "),
                    (BracedStatementBlockExpression, true, "{}"),
                ],
                "",
                0,
                0,
            ),
            (
                "  ",
                vec![(Whitespace, false, "  "), (Missing, true, "")],
                "",
                1,
                0,
            ),
            (
                " @  ",
                vec![(Whitespace, false, " "), (Error, false, "@")],
                "  ",
                0,
                1,
            ),
            (
                " @  ~   ;",
                vec![
                    (Whitespace, false, " "),
                    (Error, false, "@"),
                    (Error, false, "  "),
                    (Error, false, "~"),
                    (Whitespace, false, "   "),
                    (Semicolon, false, ";"),
                ],
                "",
                0,
                3,
            ),
            (
                " @ {}",
                vec![
                    (Whitespace, false, " "),
                    (Error, false, "@"),
                    (Whitespace, false, " "),
                    (BracedStatementBlockExpression, true, "{}"),
                ],
                "",
                0,
                1,
            ),
            (
                " @ : x",
                vec![
                    (Whitespace, false, " "),
                    (Error, false, "@"),
                    (Whitespace, false, " "),
                    (Colon, false, ":"),
                    (Statement, true, " x"),
                ],
                "",
                0,
                1,
            ),
        ] {
            let mut expected = head.clone();
            expected.extend(suffix);
            assert_shell(
                &format!("{prefix}{tail}"),
                &expected,
                pending,
                None,
                missing,
                errors,
            );
        }
        // Native first-colon Body requires physical newline; after Description
        // the native second colon also admits exactly one inline Statement.
        let (tail, body) = if prefix.ends_with('D') {
            (": x", (Statement, true, " x"))
        } else {
            (":\n  x", (IndentedStatementBlock, true, "\n  x"))
        };
        let mut expected = head;
        expected.extend([(Colon, false, ":"), body]);
        assert_shell(&format!("{prefix}{tail}"), &expected, "", None, 0, 0);
    }

    for (tail, suffix, pending, spelling, missing, errors) in [
        (" x", vec![(Statement, true, " x")], "", None, 0, 0),
        ("   ", vec![(Missing, true, "")], "   ", None, 1, 0),
        ("  ;", vec![(Missing, true, "")], "  ", Some(";"), 1, 0),
        (
            " @   ",
            vec![(Whitespace, false, " "), (Error, false, "@")],
            "   ",
            None,
            0,
            1,
        ),
        (
            " @  ~   x;",
            vec![
                (Whitespace, false, " "),
                (Error, false, "@"),
                (Error, false, "  "),
                (Error, false, "~"),
                (Statement, true, "   x"),
                (Semicolon, false, ";"),
            ],
            "",
            None,
            0,
            3,
        ),
        (
            " my x =",
            vec![(Statement, true, " my x =")],
            "",
            None,
            1,
            0,
        ),
    ] {
        let source = format!("impl 型: D:{tail}");
        let mut expected = vec![
            (ImplKw, false, "impl"),
            (Whitespace, false, " "),
            (TypeExpression, true, "型"),
            (ImplDescription, true, ": D"),
            (Colon, false, ":"),
        ];
        expected.extend(suffix);
        let node = assert_shell(&source, &expected, pending, spelling, missing, errors);
        if tail == " my x =" {
            let statement = node
                .children()
                .find(|child| child.kind() == Statement)
                .unwrap();
            let binding = statement.first_child().unwrap();
            assert_eq!(binding.kind(), BindingStatement);
            let body = binding
                .children()
                .find(|child| child.kind() == BindingBody)
                .unwrap();
            assert_impl_children(&body, &[(Missing, 19..19)]);
            assert!(!node.children().any(|child| child.kind() == Missing));
        }
    }
}

#[test]
fn impl_schema_first_colon_statement_shell_keeps_description_failure_upstream() {
    use SyntaxKind::*;
    for (source, description_children, end, missing, errors) in [
        (
            "impl 型:",
            vec![(Colon, 8..9), (TypeExpression, 9..9)],
            9,
            1,
            0,
        ),
        (
            "impl 型: @",
            vec![(Colon, 8..9), (Whitespace, 9..10), (Error, 10..11)],
            11,
            0,
            1,
        ),
    ] {
        let (green, exit, remainder) =
            run_statement_normalized(source, 100, LineEntry::InLine, None);
        assert_eq!(remainder, "");
        let root = SyntaxNode::new_root(green);
        assert_eq!(root.kind(), Root);
        assert!(root.parent().is_none());
        assert_eq!(root.to_string(), source);
        assert_impl_children(&root, &[(Statement, 0..end)]);
        let statement = root.first_child().unwrap();
        assert_impl_children(&statement, &[(ImplDeclaration, 0..end)]);
        let implementation = statement.first_child().unwrap();
        assert_impl_children(
            &implementation,
            &[
                (ImplKw, 0..4),
                (Whitespace, 4..5),
                (TypeExpression, 5..8),
                (ImplDescription, 8..end),
            ],
        );
        let description = implementation
            .children()
            .find(|node| node.kind() == ImplDescription)
            .unwrap();
        assert_impl_children(&description, &description_children);
        if missing == 1 {
            let ty = description.first_child().unwrap();
            assert_impl_children(&ty, &[(Missing, end..end)]);
        }
        for (kind, count) in [(Missing, missing), (Error, errors), (Invalid, 0)] {
            assert_eq!(
                root.descendants_with_tokens()
                    .filter(|child| child.kind() == kind)
                    .count(),
                count
            );
        }
        let mut pending = pending_item(Some(exit), LineEntry::InLine);
        assert!(pending.payload_view().is_eof());
        assert_eq!(emit_pending_leading_text(&mut pending), "");
    }
}

// Schema evidence uses ordered Rowan parentage and byte ranges, not records.
fn assert_impl_children(node: &SyntaxNode, expected: &[(SyntaxKind, std::ops::Range<u32>)]) {
    let actual = node
        .children_with_tokens()
        .map(|child| {
            assert_eq!(child.parent(), Some(node.clone()));
            let range = child.text_range();
            (
                child.kind(),
                u32::from(range.start())..u32::from(range.end()),
            )
        })
        .collect::<Vec<_>>();
    assert_eq!(actual, expected);
}

fn impl_schema_shell(source: &str, suffix: &[(SyntaxKind, std::ops::Range<u32>)]) -> SyntaxNode {
    use SyntaxKind::*;
    let (green, _, _) = run_impl_declaration(source, 0, 0, LineEntry::InLine, None);
    let node = declaration(&green);
    let mut expected = vec![(ImplKw, 0..4), (Whitespace, 4..5), (TypeExpression, 5..8)];
    expected.extend_from_slice(suffix);
    assert_impl_children(&node, &expected);
    assert!(!node.descendants().any(|child| child.kind() == Invalid));
    node
}

#[test]
fn impl_required_types_schema_distinguishes_head_and_description() {
    use SyntaxKind::*;
    let assert_elements =
        |parent: &SyntaxNode, expected: &[(SyntaxKind, bool, std::ops::Range<u32>, &str)]| {
            let children = parent.children_with_tokens().collect::<Vec<_>>();
            assert_eq!(children.len(), expected.len());
            for (child, (kind, node, range, text)) in children.iter().zip(expected) {
                assert_eq!(child.parent(), Some(parent.clone()));
                assert_eq!(child.kind(), *kind);
                assert_eq!(child.as_node().is_some(), *node);
                assert_eq!(
                    child.text_range(),
                    rowan::TextRange::new(range.start.into(), range.end.into())
                );
                assert_eq!(child.to_string(), *text);
            }
        };
    for (source, head, description, missing_at) in [
        (
            "impl ;",
            vec![(TypeExpression, true, 5..5, "")],
            vec![],
            Some(5),
        ),
        ("impl @", vec![(Error, false, 5..6, "@")], vec![], None),
        (
            "impl @ T;",
            vec![
                (Error, false, 5..6, "@"),
                (TypeExpression, true, 6..8, " T"),
            ],
            vec![],
            None,
        ),
        (
            "impl T:",
            vec![(TypeExpression, true, 5..6, "T")],
            vec![(Colon, false, 6..7, ":"), (TypeExpression, true, 7..7, "")],
            Some(7),
        ),
        (
            "impl T: @",
            vec![(TypeExpression, true, 5..6, "T")],
            vec![
                (Colon, false, 6..7, ":"),
                (Whitespace, false, 7..8, " "),
                (Error, false, 8..9, "@"),
            ],
            None,
        ),
        (
            "impl T: @ D;",
            vec![(TypeExpression, true, 5..6, "T")],
            vec![
                (Colon, false, 6..7, ":"),
                (Whitespace, false, 7..8, " "),
                (Error, false, 8..9, "@"),
                (TypeExpression, true, 9..11, " D"),
            ],
            None,
        ),
        (
            "impl T: D;",
            vec![(TypeExpression, true, 5..6, "T")],
            vec![
                (Colon, false, 6..7, ":"),
                (Whitespace, false, 7..8, " "),
                (TypeExpression, true, 8..9, "D"),
            ],
            None,
        ),
        (
            "impl @  ~   T;",
            vec![
                (Error, false, 5..6, "@"),
                (Error, false, 6..8, "  "),
                (Error, false, 8..9, "~"),
                (TypeExpression, true, 9..13, "   T"),
            ],
            vec![],
            None,
        ),
        (
            "impl T: @  ~   D;",
            vec![(TypeExpression, true, 5..6, "T")],
            vec![
                (Colon, false, 6..7, ":"),
                (Whitespace, false, 7..8, " "),
                (Error, false, 8..9, "@"),
                (Error, false, 9..11, "  "),
                (Error, false, 11..12, "~"),
                (TypeExpression, true, 12..16, "   D"),
            ],
            None,
        ),
    ] {
        let (green, exit, records, remainder) = typed_impl(source, None, 0, None);
        assert_eq!(green.to_string(), source);
        assert_eq!(remainder, "");
        let (canonical, _, canonical_remainder) =
            run_statement_normalized(source, 100, LineEntry::InLine, None);
        assert_eq!(canonical_remainder, "");
        let implementation = declaration(&canonical);
        assert_eq!(implementation.green(), declaration(&green).green());
        let statement = implementation.parent().expect("canonical Statement");
        assert_eq!(statement.kind(), Statement);
        let root = statement.parent().expect("Root");
        assert_eq!(root.kind(), Root);
        assert!(root.parent().is_none());
        assert_eq!(implementation.to_string(), source);
        assert_eq!(statement.to_string(), source);
        assert_eq!(root.to_string(), source);
        assert!(
            !root
                .descendants_with_tokens()
                .any(|child| child.kind() == Invalid)
        );

        let mut expected = vec![
            (ImplKw, false, 0..4, "impl"),
            (Whitespace, false, 4..5, " "),
        ];
        expected.extend(head.clone());
        if let Some(last) = description.last() {
            expected.push((
                ImplDescription,
                true,
                6..last.2.end,
                &source[6..last.2.end as usize],
            ));
        }
        if source.ends_with(';') {
            let end = source.len() as u32;
            expected.push((Semicolon, false, end - 1..end, ";"));
        }
        assert_elements(&implementation, &expected);
        let description_node = implementation
            .children()
            .find(|child| child.kind() == ImplDescription);
        assert_eq!(description_node.is_some(), !description.is_empty());
        if let Some(node) = &description_node {
            assert_elements(node, &description);
        }

        // Head is the phase after ImplKw and before ImplDescription/body.
        // Description Type is only inside ImplDescription after its Colon.
        // Nested Type recovery schemas are outside this owner-slot matrix.
        let mut slots = vec![(implementation.clone(), head)];
        if let Some(node) = description_node {
            assert_eq!(node.first_child_or_token().unwrap().kind(), Colon);
            slots.push((node, description));
        }
        let mut missing_count = 0;
        let mut error_count = 0;
        for (parent, slot) in slots {
            let children = parent.children_with_tokens().collect::<Vec<_>>();
            let errors = children
                .iter()
                .filter(|child| child.kind() == Error)
                .collect::<Vec<_>>();
            error_count += errors.len();
            let expected_errors = slot
                .iter()
                .filter(|child| child.0 == Error)
                .collect::<Vec<_>>();
            assert_eq!(errors.len(), expected_errors.len());
            if let (Some(first), Some(last)) = (errors.first(), errors.last()) {
                assert_eq!(
                    first.text_range().start(),
                    expected_errors[0].2.start.into()
                );
                assert_eq!(
                    last.text_range().end(),
                    expected_errors.last().unwrap().2.end.into()
                );
                for pair in errors.windows(2) {
                    assert_eq!(pair[0].text_range().end(), pair[1].text_range().start());
                }
                if let Some(retry) = parent
                    .children()
                    .find(|child| child.kind() == TypeExpression)
                {
                    assert_eq!(retry.text_range().start(), last.text_range().end());
                    let start = u32::from(retry.text_range().start());
                    let leading_len = if source.contains('~') { 3 } else { 1 };
                    let end = start + leading_len;
                    let retry_text = if parent.kind() == ImplDescription {
                        "D"
                    } else {
                        "T"
                    };
                    assert_elements(
                        &retry,
                        &[
                            (
                                Whitespace,
                                false,
                                start..end,
                                if leading_len == 3 { "   " } else { " " },
                            ),
                            (Identifier, false, end..end + 1, retry_text),
                        ],
                    );
                }
            }
            for ty in parent
                .children()
                .filter(|child| child.kind() == TypeExpression)
            {
                if ty.text_range().is_empty() {
                    let at = missing_at.expect("one absent required Type");
                    assert_eq!(ty.text_range(), rowan::TextRange::empty(at.into()));
                    assert_elements(&ty, &[(Missing, true, at..at, "")]);
                    let missing = ty.first_child().unwrap();
                    assert_eq!(missing.children_with_tokens().count(), 0);
                    missing_count += 1;
                }
            }
        }
        assert_eq!(missing_count, usize::from(missing_at.is_some()));
        assert_eq!(
            root.descendants()
                .filter(|node| node.kind() == Missing)
                .count(),
            missing_count
        );
        assert_eq!(
            root.descendants_with_tokens()
                .filter(|child| child.kind() == Error)
                .count(),
            error_count
        );
        let mut item = pending_item(exit, LineEntry::InLine);
        assert!(item.payload_view().is_eof());
        assert_eq!(emit_pending_leading_text(&mut item), "");

        // Frozen records are compatibility evidence, not a slot classifier.
        assert_eq!(
            records.len(),
            usize::from(missing_at.is_some() || error_count != 0)
        );
        let (again, again_exit, frozen, again_remainder) =
            typed_impl(source, Some(&records), 0, None);
        assert_eq!(again, green);
        assert_eq!(frozen, records);
        assert_eq!(again_remainder, remainder);
        let mut item = pending_item(again_exit, LineEntry::InLine);
        assert!(item.payload_view().is_eof());
        assert_eq!(emit_pending_leading_text(&mut item), "");
    }
}

#[test]
fn impl_schema_completed_head_or_description_selects_body_introducer() {
    use SyntaxKind::*;
    for (prefix, base) in [("impl 型", 8), ("impl 型: D", 11)] {
        for (tail, suffix) in [
            (";", vec![(Semicolon, 0..1)]),
            (
                " {}",
                vec![(Whitespace, 0..1), (BracedStatementBlockExpression, 1..3)],
            ),
            ("  ", vec![(Whitespace, 0..2), (Missing, 2..2)]),
            ("\r\n", vec![(Missing, 0..0)]),
            ("  )", vec![(Missing, 0..0)]),
            (" @  ", vec![(Whitespace, 0..1), (Error, 1..2)]),
            (" @\r\nnext", vec![(Whitespace, 0..1), (Error, 1..2)]),
            (" @  )", vec![(Whitespace, 0..1), (Error, 1..2)]),
            (
                " @  ~   ;",
                vec![
                    (Whitespace, 0..1),
                    (Error, 1..2),
                    (Error, 2..4),
                    (Error, 4..5),
                    (Whitespace, 5..8),
                    (Semicolon, 8..9),
                ],
            ),
            (
                " @ {}",
                vec![
                    (Whitespace, 0..1),
                    (Error, 1..2),
                    (Whitespace, 2..3),
                    (BracedStatementBlockExpression, 3..5),
                ],
            ),
            (
                " @ : x",
                vec![
                    (Whitespace, 0..1),
                    (Error, 1..2),
                    (Whitespace, 2..3),
                    (Colon, 3..4),
                    (Statement, 4..6),
                ],
            ),
        ] {
            let mut expected = if base == 11 {
                vec![(ImplDescription, 8..11)]
            } else {
                vec![]
            };
            expected.extend(
                suffix
                    .into_iter()
                    .map(|(kind, range)| (kind, base + range.start..base + range.end)),
            );
            let node = impl_schema_shell(&format!("{prefix}{tail}"), &expected);
            if let Some(description) = node
                .children()
                .find(|child| child.kind() == ImplDescription)
            {
                assert_impl_children(
                    &description,
                    &[(Colon, 8..9), (Whitespace, 9..10), (TypeExpression, 10..11)],
                );
            }
        }
    }
}

#[test]
fn impl_schema_second_colon_selects_inline_body() {
    use SyntaxKind::*;
    for (tail, suffix) in [
        (" x", vec![(Statement, 12..14)]),
        ("   ", vec![(Missing, 12..12)]),
        ("  ;", vec![(Missing, 12..12)]),
        ("\r\nnext", vec![(Missing, 12..12)]),
        ("  ]", vec![(Missing, 12..12)]),
        (" @   ", vec![(Whitespace, 12..13), (Error, 13..14)]),
        (" @  ]", vec![(Whitespace, 12..13), (Error, 13..14)]),
        (
            " @  ~   x;",
            vec![
                (Whitespace, 12..13),
                (Error, 13..14),
                (Error, 14..16),
                (Error, 16..17),
                (Statement, 17..21),
                (Semicolon, 21..22),
            ],
        ),
    ] {
        let mut expected = vec![(ImplDescription, 8..11), (Colon, 11..12)];
        expected.extend(suffix);
        let node = impl_schema_shell(&format!("impl 型: D:{tail}"), &expected);
        let description = node
            .children()
            .find(|child| child.kind() == ImplDescription)
            .unwrap();
        assert_impl_children(
            &description,
            &[(Colon, 8..9), (Whitespace, 9..10), (TypeExpression, 10..11)],
        );
        if let Some(statement) = node.children().find(|child| child.kind() == Statement) {
            let leading = statement.first_token().unwrap();
            assert_eq!(leading.kind(), Whitespace);
            let start = statement.text_range().start();
            let width = if tail == " x" { 1 } else { 3 };
            assert_eq!(
                leading.text_range(),
                rowan::TextRange::new(start, start + rowan::TextSize::from(width))
            );
        }
    }
}

#[test]
fn impl_schema_first_colon_absence_and_malformed_description_stay_upstream() {
    use SyntaxKind::*;
    for (tail, description_children, end) in [
        (":", vec![(Colon, 8..9), (TypeExpression, 9..9)], 9),
        (
            ": )",
            vec![(Colon, 8..9), (Whitespace, 9..10), (TypeExpression, 10..10)],
            10,
        ),
        (
            ": @ ;",
            vec![(Colon, 8..9), (Whitespace, 9..10), (Error, 10..11)],
            11,
        ),
    ] {
        let node = impl_schema_shell(&format!("impl 型{tail}"), &[(ImplDescription, 8..end)]);
        let description = node
            .children()
            .find(|child| child.kind() == ImplDescription)
            .unwrap();
        assert_impl_children(&description, &description_children);
        for ty in description
            .children()
            .filter(|child| child.kind() == TypeExpression)
        {
            assert_impl_children(&ty, &[(Missing, end..end)]);
        }
    }
}

#[test]
fn impl_schema_inline_binding_missing_remains_child_owned() {
    use SyntaxKind::*;
    let node = impl_schema_shell(
        "impl 型: D: my x =",
        &[
            (ImplDescription, 8..11),
            (Colon, 11..12),
            (Statement, 12..19),
        ],
    );
    let statement = node
        .children()
        .find(|child| child.kind() == Statement)
        .unwrap();
    let binding = statement
        .children()
        .find(|child| child.kind() == BindingStatement)
        .unwrap();
    let body = binding
        .children()
        .find(|child| child.kind() == BindingBody)
        .unwrap();
    assert_impl_children(&body, &[(Missing, 19..19)]);
}

#[test]
fn impl_first_colon_absence_is_description_without_body_cascade() {
    use crate::recovery_record::{
        DeclarationRole, ExpectedSyntax, GrammarRole, ImplRole, RecoveryKind,
    };
    for (source, slot, expected) in [
        (
            "impl T:",
            ImplRole::Description,
            ExpectedSyntax::TypeExpression,
        ),
        ("impl T: D:", ImplRole::Body, ExpectedSyntax::Statement),
    ] {
        let (green, _, records, rest) = typed_impl(source, None, 0, None);
        assert_eq!(green.to_string(), source);
        assert_eq!(rest, "");
        assert_eq!(records.len(), 1);
        assert_eq!(
            records[0].site.role,
            GrammarRole::Declaration(DeclarationRole::Impl(slot))
        );
        assert_eq!(records[0].kind, RecoveryKind::Missing);
        assert_eq!(
            records[0].site.range,
            100 + source.len()..100 + source.len()
        );
        assert_eq!(records[0].expectations[0].expected, expected);
        let (again, _, frozen, rest) = typed_impl(source, Some(&records), 0, None);
        assert_eq!(again, green);
        assert_eq!(frozen, records);
        assert_eq!(rest, "");
    }
}

#[test]
fn impl_body_protected_fence_and_contextual_stop_reconcile_exact_handoff() {
    use crate::lexical::yumark::{FenceOpener, FencePrefixPolicy};
    let fence = FenceBoundary {
        opener: FenceOpener {
            line: 0,
            marker: 0..3,
            marker_width: 3,
        },
        prefix_policy: FencePrefixPolicy::ActivePrefixQuote { depth: 2, base: 0 },
        close_column: 0,
    };
    for (source, owned) in [
        ("impl T\r\n> > ```\r\nouter", "impl T"),
        ("impl T: D:\r\n> > ```\r\nouter", "impl T: D:"),
        ("impl T @\r\n> > ```\r\nouter", "impl T @"),
        ("impl T: D: @\r\n> > ```\r\nouter", "impl T: D: @"),
    ] {
        let (green, exit, records, remainder) = typed_impl(source, None, 0, Some(&fence));
        assert_eq!(green.to_string(), owned);
        assert_eq!(records.len(), 1);
        let item = pending_item(exit, LineEntry::PhysicalStart);
        let (leading, boundary) = emit_terminal_leading_text(item);
        assert_eq!(leading, "\r\n");
        assert_eq!(boundary.coordinate(), 100 + owned.len() + 2);
        if records[0].kind == crate::recovery_record::RecoveryKind::Missing {
            assert_eq!(
                records[0].site.range,
                boundary.coordinate()..boundary.coordinate()
            );
        }
        assert_eq!(remainder, "> > ```\r\nouter");
        let (again, exit, frozen, remainder) = typed_impl(source, Some(&records), 0, Some(&fence));
        assert_eq!(again, green);
        assert_eq!(frozen, records);
        assert_eq!(remainder, "> > ```\r\nouter");
        let (leading, boundary) =
            emit_terminal_leading_text(pending_item(exit, LineEntry::PhysicalStart));
        assert_eq!(leading, "\r\n");
        assert_eq!(boundary.coordinate(), 100 + owned.len() + 2);
    }
    for owned in ["impl T", "impl T: D:", "impl T @", "impl T: D: @"] {
        let source = format!("{owned}  else suffix");
        let (green, exit, records, remainder) = typed_impl(&source, None, STOP_ELSE, None);
        assert_eq!(green.to_string(), owned);
        assert_eq!(records.len(), 1);
        assert_eq!(remainder, " suffix");
        let mut item = pending_item(exit, LineEntry::InLine);
        assert_eq!(emit_pending_leading_text(&mut item), "  ");
        assert_eq!(item.payload_view().spelling(), Some("else"));
        let (again, exit, frozen, remainder) = typed_impl(&source, Some(&records), STOP_ELSE, None);
        assert_eq!(again, green);
        assert_eq!(frozen, records);
        assert_eq!(remainder, " suffix");
        let mut item = pending_item(exit, LineEntry::InLine);
        assert_eq!(emit_pending_leading_text(&mut item), "  ");
        assert_eq!(item.payload_view().spelling(), Some("else"));
    }
}

#[test]
fn impl_body_recovery_retains_head_and_statement_child_owners() {
    use crate::recovery_record::{BindingRole, DeclarationRole, GrammarRole, ImplRole};
    for (source, role) in [
        (
            "impl @ ;",
            GrammarRole::Type(crate::recovery_record::TypeRole::Primary),
        ),
        (
            "impl )",
            GrammarRole::Declaration(DeclarationRole::Impl(ImplRole::Head)),
        ),
    ] {
        let (_, _, records, _) = typed_impl(source, None, 0, None);
        assert_eq!(records.len(), 1, "{source}");
        assert_eq!(records[0].site.role, role);
    }
    for source in [
        "impl T: D: my x =",
        "impl T {my x =}",
        "impl T: D:\n  my x =",
    ] {
        let (green, _, records, _) = typed_impl(source, None, 0, None);
        assert_eq!(records.len(), 1, "{source}");
        assert_eq!(
            records[0].site.role,
            GrammarRole::Declaration(DeclarationRole::Binding(BindingRole::Body))
        );
        let (again, _, frozen, _) = typed_impl(source, Some(&records), 0, None);
        assert_eq!(again, green);
        assert_eq!(frozen, records);
    }
}

fn typed_impl<'s>(
    source: &'s str,
    frozen: Option<&[CommittedRecoveryRecord]>,
    stops: Stops,
    fence: Option<&FenceBoundary>,
) -> (
    GreenNode,
    Option<NormalizedExit>,
    Vec<CommittedRecoveryRecord>,
    &'s str,
) {
    let operators = OperatorTable::empty();
    let mut input = source;
    let mut recover = Recover::new_for_test(&operators);
    let mut builder = frozen.map_or_else(GreenNodeBuilder::new, |records| {
        recover = Recover::reconcile_for_test(recover.operators(), records);
        GreenNodeBuilder::new()
    });
    builder.start_node(SyntaxKind::Root.into());
    let exit = impl_declaration_witness(
        crate::cursor::SyntaxIn::new(&mut input, &mut recover, &mut builder),
        0,
        stops,
        crate::statement::StatementLineHandoff::OrdinaryLayout,
        100,
        LineEntry::InLine,
        fence,
    );
    builder.finish_node();
    let (green, records) = (builder.finish(), recover.finish_recoveries_for_test());
    (green, exit, records, input)
}

#[test]
fn impl_body_introducer_eof_retains_equal_indent_newline() {
    use crate::recovery_record::{DeclarationRole, GrammarRole, ImplRole, RecoveryKind};
    for owned in ["impl T", "impl T: D"] {
        let source = format!("{owned}\r\n");
        let (green, exit, records, remainder) = typed_impl(&source, None, 0, None);
        assert_eq!(green.to_string(), owned);
        assert_eq!(remainder, "");
        assert_eq!(records.len(), 1);
        assert_eq!(records[0].kind, RecoveryKind::Missing);
        assert_eq!(
            records[0].site.role,
            GrammarRole::Declaration(DeclarationRole::Impl(ImplRole::BodyIntroducer))
        );
        let anchor = 100 + owned.len();
        assert_eq!(records[0].site.range, anchor..anchor);
        let mut item = pending_item(exit, LineEntry::InLine);
        assert!(item.payload_view().is_eof());
        assert_eq!(emit_pending_leading_text(&mut item), "\r\n");
        let (again, exit, frozen, remainder) = typed_impl(&source, Some(&records), 0, None);
        assert_eq!(again, green);
        assert_eq!(frozen, records);
        assert_eq!(remainder, "");
        let mut item = pending_item(exit, LineEntry::InLine);
        assert!(item.payload_view().is_eof());
        assert_eq!(emit_pending_leading_text(&mut item), "\r\n");
    }
}

#[test]
fn impl_body_records_are_exact_and_frozen_with_leading_ownership() {
    use crate::recovery_record::{
        DeclarationRole, Delimiter, DiagnosticId, ExpectationSources, ExpectedSyntax, GrammarRole,
        ImplRole as Role, PunctuationEvidence, RecoveryKind, RecoverySiteKey, SyntaxExpectation,
        UnexpectedCategory, UnexpectedSyntax,
    };
    use std::sync::Arc;
    for (source, slot, kind, range, owned, leading) in [
        (
            "impl T   ",
            Role::BodyIntroducer,
            RecoveryKind::Missing,
            9..9,
            "impl T   ",
            "",
        ),
        (
            "impl T  )",
            Role::BodyIntroducer,
            RecoveryKind::Missing,
            6..6,
            "impl T",
            "  ",
        ),
        (
            "impl T @  ~   ;",
            Role::BodyIntroducer,
            RecoveryKind::Error,
            7..11,
            "impl T @  ~   ;",
            "",
        ),
        (
            "impl T @ {}",
            Role::BodyIntroducer,
            RecoveryKind::Error,
            7..8,
            "impl T @ {}",
            "",
        ),
        (
            "impl T @ : x",
            Role::BodyIntroducer,
            RecoveryKind::Error,
            7..8,
            "impl T @ : x",
            "",
        ),
        (
            "impl T @   ",
            Role::BodyIntroducer,
            RecoveryKind::Error,
            7..8,
            "impl T @",
            "   ",
        ),
        (
            "impl T @  )",
            Role::BodyIntroducer,
            RecoveryKind::Error,
            7..8,
            "impl T @",
            "  ",
        ),
        (
            "impl T: D:   ",
            Role::Body,
            RecoveryKind::Missing,
            10..10,
            "impl T: D:",
            "   ",
        ),
        (
            "impl T: D:  ;",
            Role::Body,
            RecoveryKind::Missing,
            10..10,
            "impl T: D:",
            "  ",
        ),
        (
            "impl T: D:\r\nnext",
            Role::Body,
            RecoveryKind::Missing,
            10..10,
            "impl T: D:",
            "\r\n",
        ),
        (
            "impl T: D:  ]",
            Role::Body,
            RecoveryKind::Missing,
            10..10,
            "impl T: D:",
            "  ",
        ),
        (
            "impl T: D: @  ~   x",
            Role::Body,
            RecoveryKind::Error,
            11..15,
            "impl T: D: @  ~   x",
            "",
        ),
        (
            "impl T: D: @  ;",
            Role::Body,
            RecoveryKind::Error,
            11..12,
            "impl T: D: @",
            "  ",
        ),
        (
            "impl T: D: @   ",
            Role::Body,
            RecoveryKind::Error,
            11..12,
            "impl T: D: @",
            "   ",
        ),
        (
            "impl 型: D: @   ]",
            Role::Body,
            RecoveryKind::Error,
            13..14,
            "impl 型: D: @",
            "   ",
        ),
    ] {
        let (green, exit, records, remainder) = typed_impl(source, None, 0, None);
        assert_eq!(green.to_string(), owned, "{source:?}");
        let mut item = pending_item(exit, LineEntry::InLine);
        assert_eq!(emit_pending_leading_text(&mut item), leading, "{source:?}");
        let role = GrammarRole::Declaration(DeclarationRole::Impl(slot));
        let range = 100 + range.start..100 + range.end;
        let expected = if slot == Role::Body {
            vec![ExpectedSyntax::Statement]
        } else {
            vec![
                ExpectedSyntax::Punctuation(PunctuationEvidence::Semicolon),
                ExpectedSyntax::Punctuation(PunctuationEvidence::Open(Delimiter::Brace)),
                ExpectedSyntax::Punctuation(PunctuationEvidence::Colon),
            ]
        };
        assert_eq!(
            records,
            [CommittedRecoveryRecord {
                id: DiagnosticId(0),
                site: RecoverySiteKey {
                    role,
                    range: range.clone()
                },
                kind,
                unexpected: if kind == RecoveryKind::Error {
                    Arc::from([UnexpectedSyntax::Token {
                        range: range.clone(),
                        category: UnexpectedCategory::OtherCharacter,
                    }])
                } else {
                    Arc::from([])
                },
                expectations: expected
                    .into_iter()
                    .map(|expected| SyntaxExpectation {
                        role,
                        expected,
                        range: range.clone(),
                        sources: ExpectationSources::COMMITTED_RECOVERY_RULE
                    })
                    .collect::<Vec<_>>()
                    .into(),
                primary_expectation: 0
            }],
            "{source:?}"
        );
        let mut seed = records;
        seed[0].id = DiagnosticId(73);
        let (again, exit, frozen, again_remainder) = typed_impl(source, Some(&seed), 0, None);
        assert_eq!(again, green);
        assert_eq!(frozen, seed);
        assert_eq!(again_remainder, remainder);
        let mut item = pending_item(exit, LineEntry::InLine);
        assert_eq!(emit_pending_leading_text(&mut item), leading);
    }
}

fn declaration(green: &GreenNode) -> SyntaxNode {
    SyntaxNode::new_root(green.clone())
        .descendants()
        .find(|node| node.kind() == SyntaxKind::ImplDeclaration)
        .expect("ImplDeclaration")
}

fn count(node: &SyntaxNode, kind: SyntaxKind) -> usize {
    if kind == SyntaxKind::Error {
        return crate::tests::recovery_output::recovery_groups(node).len();
    }
    node.descendants()
        .filter(|node| node.kind() == kind)
        .count()
}

fn token_count(node: &SyntaxNode, kind: SyntaxKind) -> usize {
    node.descendants_with_tokens()
        .filter_map(|element| element.into_token())
        .filter(|token| token.kind() == kind)
        .count()
}

fn pending_item(exit: Option<NormalizedExit>, line_entry: LineEntry) -> Item {
    match exit {
        Some(NormalizedExit::Complete(Err(Either::Left(item)), actual)) => {
            assert_eq!(actual, line_entry);
            item
        }
        Some(NormalizedExit::Complete(Err(Either::Right(end)), actual)) => {
            assert_eq!(actual, line_entry);
            end.item
        }
        _ => panic!("an Item must remain pending"),
    }
}

fn pending_tokens(
    exit: Option<NormalizedExit>,
    spelling: &str,
    line_entry: LineEntry,
) -> Vec<(SyntaxKind, String)> {
    let mut item = pending_item(exit, line_entry);
    assert_eq!(item.payload_view().spelling(), Some(spelling));
    let mut builder = GreenNodeBuilder::new();
    builder.start_node(SyntaxKind::Root.into());
    item.emit_all_remaining_leading(&mut builder);
    item.emit_payload(&mut builder, SyntaxKind::Identifier);
    builder.finish_node();
    SyntaxNode::new_root(builder.finish())
        .children_with_tokens()
        .filter_map(|element| element.into_token())
        .map(|token| (token.kind(), token.text().to_owned()))
        .collect()
}

fn pending_token_leading(
    exit: Option<NormalizedExit>,
    kind: TokenKind,
    spelling: &str,
    line_entry: LineEntry,
) -> Vec<(SyntaxKind, String)> {
    let mut item = pending_item(exit, line_entry);
    assert_eq!(item.payload_view().token_kind(), Some(kind));
    assert_eq!(item.payload_view().spelling(), Some(spelling));
    let mut builder = GreenNodeBuilder::new();
    builder.start_node(SyntaxKind::Root.into());
    item.emit_all_remaining_leading(&mut builder);
    builder.finish_node();
    SyntaxNode::new_root(builder.finish())
        .children_with_tokens()
        .filter_map(|element| element.into_token())
        .map(|token| (token.kind(), token.text().to_owned()))
        .collect()
}

#[test]
fn impl_private_owner_builds_description_and_each_body_form_losslessly() {
    for (source, descriptions, braced, indented) in [
        ("impl T;", 0, 0, 0),
        ("impl T { my x = y }", 0, 1, 0),
        ("impl T:\n  my x = y", 0, 0, 1),
        ("impl T: D;", 1, 0, 0),
        ("impl T: D: my x = y;", 1, 0, 0),
        ("impl T: D:\n  my x = y", 1, 0, 1),
        ("impl T: { value: Int };", 1, 0, 0),
        ("impl T: { value: Int }: my x = y", 1, 0, 0),
    ] {
        let (green, exit, remainder) = run_impl_declaration(source, 0, 0, LineEntry::InLine, None);
        assert!(exit.is_some(), "{source:?}");
        assert_eq!(green.to_string(), source, "{source:?}");
        assert_eq!(remainder, "", "{source:?}");
        let node = declaration(&green);
        assert_eq!(
            count(&node, SyntaxKind::ImplDescription),
            descriptions,
            "{source:?}\n{node:#?}"
        );
        assert_eq!(
            count(&node, SyntaxKind::BracedStatementBlockExpression),
            braced,
            "{source:?}\n{node:#?}"
        );
        assert_eq!(
            count(&node, SyntaxKind::IndentedStatementBlock),
            indented,
            "{source:?}\n{node:#?}"
        );
        assert_eq!(
            count(&node, SyntaxKind::Missing),
            0,
            "{source:?}\n{node:#?}"
        );
        assert_eq!(count(&node, SyntaxKind::Error), 0, "{source:?}\n{node:#?}");
    }

    let (green, _, _) = run_impl_declaration("impl T: D;", 0, 0, LineEntry::InLine, None);
    assert_eq!(
        declaration(&green)
            .children_with_tokens()
            .map(|element| element.kind())
            .collect::<Vec<_>>(),
        [
            SyntaxKind::ImplKw,
            SyntaxKind::Whitespace,
            SyntaxKind::TypeExpression,
            SyntaxKind::ImplDescription,
            SyntaxKind::Semicolon
        ]
    );
    let description = declaration(&green)
        .children()
        .find(|node| node.kind() == SyntaxKind::ImplDescription)
        .expect("ImplDescription");
    assert_eq!(
        description
            .children_with_tokens()
            .map(|element| element.kind())
            .collect::<Vec<_>>(),
        [
            SyntaxKind::Colon,
            SyntaxKind::Whitespace,
            SyntaxKind::TypeExpression
        ]
    );
}

#[test]
fn impl_intro_is_exact_and_visibility_led_rejections_roll_back() {
    for source in ["impl T;", "my impl T;", "our impl T;", "pub impl T;"] {
        let (green, exit, _) = run_impl_declaration(source, 0, 0, LineEntry::InLine, None);
        assert!(exit.is_some(), "{source:?}");
        assert_eq!(green.to_string(), source, "{source:?}");
        assert_eq!(token_count(&declaration(&green), SyntaxKind::ImplKw), 1);
    }
    for source in [
        "implement T;",
        "implish T;",
        "myimpl T;",
        "my implish T;",
        "pub implement T;",
        "our\nimpl T;",
        "\nimpl T;",
    ] {
        let (green, exit, remainder) =
            run_impl_declaration(source, 0, 700, LineEntry::InLine, None);
        assert!(exit.is_none(), "{source:?}");
        assert_eq!(green.to_string(), "", "{source:?}");
        assert_eq!(remainder, source, "{source:?}");
    }
    for source in ["impl(T);", "pub\n  impl\n    T;"] {
        let (green, exit, _) = run_impl_declaration(source, 0, 0, LineEntry::InLine, None);
        assert!(exit.is_some(), "{source:?}");
        assert_eq!(green.to_string(), source, "{source:?}");
    }
    let (green, exit, _) = run_impl_declaration("my impl = value", 0, 0, LineEntry::InLine, None);
    assert!(exit.is_some());
    assert_eq!(token_count(&declaration(&green), SyntaxKind::ImplKw), 1);
    assert_eq!(count(&declaration(&green), SyntaxKind::BindingStatement), 0);
}

#[test]
fn impl_head_and_description_use_full_nested_type_surface() {
    for source in [
        "impl F (A->B) 't;",
        "impl F(A -> B) 't;",
        "impl :{A};",
        "impl '[io];",
        "impl [io] Task;",
        "impl ({ value: T });",
        "impl T: for 'a: ('a -> :{Some 'a});",
        "impl T: '[io];",
        "impl T: [io] Task;",
    ] {
        let (green, _, remainder) = run_impl_declaration(source, 0, 0, LineEntry::InLine, None);
        assert_eq!(green.to_string(), source, "{source:?}");
        assert_eq!(remainder, "", "{source:?}");
        let node = declaration(&green);
        assert_eq!(
            count(&node, SyntaxKind::Missing),
            0,
            "{source:?}\n{node:#?}"
        );
        assert_eq!(count(&node, SyntaxKind::Error), 0, "{source:?}\n{node:#?}");
    }
    let (green, _, _) =
        run_impl_declaration("impl T: { value: Int };", 0, 0, LineEntry::InLine, None);
    let node = declaration(&green);
    let description = node
        .children()
        .find(|child| child.kind() == SyntaxKind::ImplDescription)
        .expect("description");
    assert_eq!(count(&description, SyntaxKind::NamedRecordType), 1);
    assert_eq!(count(&node, SyntaxKind::BracedStatementBlockExpression), 0);
}

#[test]
fn impl_head_retains_inherited_type_ml_stop_before_spaced_arrow() {
    let source = "impl F (A -> B) 't;";
    let (green, _, remainder) = run_impl_declaration(source, 0, 0, LineEntry::InLine, None);
    assert_eq!(green.to_string(), source);
    assert_eq!(remainder, "");
    let node = declaration(&green);
    assert_eq!(
        node.children()
            .filter(|child| child.kind() == SyntaxKind::TypeExpression)
            .count(),
        1
    );
    assert_eq!(count(&node, SyntaxKind::Missing), 0, "{node:#?}");
    assert_eq!(count(&node, SyntaxKind::Error), 1, "{node:#?}");
    let error = crate::tests::recovery_output::recovery_groups(&node)
        .into_iter()
        .next()
        .expect("spaced arrow is not a tail in inherited Type-ML");
    assert_eq!(error.to_string(), "->");
    assert_eq!(usize::from(error.text_range().start()), 10);
    assert_eq!(usize::from(error.text_range().end()), 12);
    assert_eq!(
        error.parent().unwrap().kind(),
        SyntaxKind::ParenthesizedTypeGroup
    );
}

#[test]
fn impl_description_owns_only_its_fresh_bare_record_primary() {
    for source in [
        "impl T: {} {}",
        "impl T: { value: Int } { my x = y }",
        "impl T: F ({ value: Int }) {}",
    ] {
        let (green, _, remainder) = run_impl_declaration(source, 0, 0, LineEntry::InLine, None);
        assert_eq!(green.to_string(), source, "{source:?}");
        assert_eq!(remainder, "", "{source:?}");
        let node = declaration(&green);
        let description = node
            .children()
            .find(|child| child.kind() == SyntaxKind::ImplDescription)
            .expect("ImplDescription");
        assert_eq!(count(&description, SyntaxKind::NamedRecordType), 1);
        assert_eq!(count(&node, SyntaxKind::BracedStatementBlockExpression), 1);
        assert_eq!(
            count(&node, SyntaxKind::Missing),
            0,
            "{source:?}\n{node:#?}"
        );
        assert_eq!(count(&node, SyntaxKind::Error), 0, "{source:?}\n{node:#?}");
    }

    for source in ["impl T: {};", "impl T: {}: my x = y"] {
        let (green, _, remainder) = run_impl_declaration(source, 0, 0, LineEntry::InLine, None);
        assert_eq!(green.to_string(), source, "{source:?}");
        assert_eq!(remainder, "", "{source:?}");
        let node = declaration(&green);
        let description = node
            .children()
            .find(|child| child.kind() == SyntaxKind::ImplDescription)
            .expect("ImplDescription");
        assert_eq!(count(&description, SyntaxKind::NamedRecordType), 1);
        assert_eq!(count(&node, SyntaxKind::BracedStatementBlockExpression), 0);
        assert_eq!(
            count(&node, SyntaxKind::Missing),
            0,
            "{source:?}\n{node:#?}"
        );
        assert_eq!(count(&node, SyntaxKind::Error), 0, "{source:?}\n{node:#?}");
    }

    let source = "impl T: :{A} {}";
    let (green, _, remainder) = run_impl_declaration(source, 0, 0, LineEntry::InLine, None);
    assert_eq!(green.to_string(), source);
    assert_eq!(remainder, "");
    let node = declaration(&green);
    let description = node
        .children()
        .find(|child| child.kind() == SyntaxKind::ImplDescription)
        .expect("ImplDescription");
    assert_eq!(count(&description, SyntaxKind::PolymorphicVariantType), 1);
    assert_eq!(count(&description, SyntaxKind::NamedRecordType), 0);
    assert_eq!(count(&node, SyntaxKind::BracedStatementBlockExpression), 1);
    assert_eq!(count(&node, SyntaxKind::Missing), 0, "{node:#?}");
    assert_eq!(count(&node, SyntaxKind::Error), 0, "{node:#?}");

    let source = "impl T: @ { value: Int };";
    let (green, _, remainder) = run_impl_declaration(source, 0, 0, LineEntry::InLine, None);
    assert_eq!(green.to_string(), source);
    assert_eq!(remainder, "");
    let node = declaration(&green);
    let description = node
        .children()
        .find(|child| child.kind() == SyntaxKind::ImplDescription)
        .expect("ImplDescription");
    assert_eq!(count(&description, SyntaxKind::Error), 1);
    assert_eq!(count(&description, SyntaxKind::NamedRecordType), 1);
    assert_eq!(count(&node, SyntaxKind::BracedStatementBlockExpression), 0);
    assert_eq!(count(&node, SyntaxKind::Missing), 0, "{node:#?}");

    let (green, _, _) = run_impl_declaration("impl {}", 0, 0, LineEntry::InLine, None);
    let node = declaration(&green);
    assert_eq!(count(&node, SyntaxKind::ImplDescription), 0);
    assert_eq!(count(&node, SyntaxKind::NamedRecordType), 0);
    assert_eq!(count(&node, SyntaxKind::BracedStatementBlockExpression), 1);
    assert_eq!(count(&node, SyntaxKind::Missing), 1, "{node:#?}");

    let (green, _, _) = run_impl_declaration("impl T {}", 0, 0, LineEntry::InLine, None);
    let node = declaration(&green);
    assert_eq!(count(&node, SyntaxKind::ImplDescription), 0);
    assert_eq!(count(&node, SyntaxKind::NamedRecordType), 0);
    assert_eq!(count(&node, SyntaxKind::BracedStatementBlockExpression), 1);
    assert_eq!(count(&node, SyntaxKind::Missing), 0, "{node:#?}");

    let lbrace_stop = crate::lexical::stops::STOP_LBRACE;
    for source in ["impl T: {};", "impl T: @ {};"] {
        let (green, _, remainder) =
            run_impl_declaration(source, lbrace_stop, 0, LineEntry::InLine, None);
        assert_eq!(green.to_string(), source, "{source:?}");
        assert_eq!(remainder, "", "{source:?}");
        let node = declaration(&green);
        let description = node
            .children()
            .find(|child| child.kind() == SyntaxKind::ImplDescription)
            .expect("ImplDescription");
        assert_eq!(count(&description, SyntaxKind::NamedRecordType), 1);
        assert_eq!(
            count(&node, SyntaxKind::Missing),
            0,
            "{source:?}\n{node:#?}"
        );
        assert_eq!(
            count(&node, SyntaxKind::Error),
            usize::from(source.contains('@')),
            "{source:?}\n{node:#?}"
        );
    }

    let source = "impl T: {} {}";
    let (green, _, remainder) =
        run_impl_declaration(source, lbrace_stop, 0, LineEntry::InLine, None);
    assert_eq!(green.to_string(), source);
    assert_eq!(remainder, "");
    let node = declaration(&green);
    assert_eq!(count(&node, SyntaxKind::NamedRecordType), 1);
    assert_eq!(count(&node, SyntaxKind::BracedStatementBlockExpression), 1);
    assert_eq!(count(&node, SyntaxKind::Missing), 0, "{node:#?}");

    let (green, _, _) = run_impl_declaration("impl {}", lbrace_stop, 0, LineEntry::InLine, None);
    let node = declaration(&green);
    assert_eq!(count(&node, SyntaxKind::NamedRecordType), 0);
    assert_eq!(count(&node, SyntaxKind::BracedStatementBlockExpression), 1);
    assert_eq!(count(&node, SyntaxKind::Missing), 1, "{node:#?}");
}

#[test]
fn impl_missing_head_retries_only_its_original_body_starter() {
    for (source, braced, description) in [
        ("impl;", 0, 0),
        ("impl{}", 1, 0),
        ("impl:\n  my x = y", 0, 0),
        ("impl: D;", 0, 1),
    ] {
        let (green, _, remainder) = run_impl_declaration(source, 0, 0, LineEntry::InLine, None);
        assert_eq!(green.to_string(), source, "{source:?}");
        assert_eq!(remainder, "", "{source:?}");
        let node = declaration(&green);
        assert_eq!(
            count(&node, SyntaxKind::Missing),
            1,
            "{source:?}\n{node:#?}"
        );
        assert_eq!(count(&node, SyntaxKind::Error), 0, "{source:?}\n{node:#?}");
        assert_eq!(
            count(&node, SyntaxKind::BracedStatementBlockExpression),
            braced
        );
        assert_eq!(count(&node, SyntaxKind::ImplDescription), description);
    }
    for (source, kind, spelling, remainder) in [
        ("impl @;", TokenKind::Semicolon, ";", ""),
        ("impl @{}", TokenKind::LBrace, "{", "}"),
        ("impl @:", TokenKind::Colon, ":", ""),
    ] {
        let (green, exit, actual_remainder) =
            run_impl_declaration(source, 0, 0, LineEntry::InLine, None);
        assert_eq!(green.to_string(), "impl @", "{source:?}");
        assert_eq!(actual_remainder, remainder, "{source:?}");
        let node = declaration(&green);
        assert_eq!(count(&node, SyntaxKind::Error), 1, "{source:?}\n{node:#?}");
        assert_eq!(
            count(&node, SyntaxKind::Missing),
            0,
            "{source:?}\n{node:#?}"
        );
        assert_eq!(
            pending_token_leading(exit, kind, spelling, LineEntry::InLine),
            []
        );
    }
}

#[test]
fn impl_description_missing_and_malformed_recovery_does_not_cascade() {
    for source in ["impl T: ;", "impl T: : my x = y"] {
        let (green, _, remainder) = run_impl_declaration(source, 0, 0, LineEntry::InLine, None);
        assert_eq!(green.to_string(), source, "{source:?}");
        assert_eq!(remainder, "", "{source:?}");
        let node = declaration(&green);
        assert_eq!(count(&node, SyntaxKind::ImplDescription), 1);
        assert_eq!(
            count(&node, SyntaxKind::Missing),
            1,
            "{source:?}\n{node:#?}"
        );
        assert_eq!(count(&node, SyntaxKind::Error), 0, "{source:?}\n{node:#?}");
    }
    let source = "impl T: @ D;";
    let (green, _, remainder) = run_impl_declaration(source, 0, 0, LineEntry::InLine, None);
    assert_eq!(green.to_string(), source);
    assert_eq!(remainder, "");
    let node = declaration(&green);
    assert_eq!(count(&node, SyntaxKind::ImplDescription), 1);
    assert_eq!(count(&node, SyntaxKind::Error), 1, "{node:#?}");
    assert_eq!(count(&node, SyntaxKind::Missing), 0, "{node:#?}");

    for (source, kind, spelling, remainder) in [
        ("impl T: @;", TokenKind::Semicolon, ";", ""),
        ("impl T: @:", TokenKind::Colon, ":", ""),
    ] {
        let (green, exit, actual_remainder) =
            run_impl_declaration(source, 0, 0, LineEntry::InLine, None);
        assert_eq!(actual_remainder, remainder, "{source:?}");
        let node = declaration(&green);
        assert_eq!(count(&node, SyntaxKind::ImplDescription), 1);
        assert_eq!(count(&node, SyntaxKind::Error), 1, "{source:?}\n{node:#?}");
        assert_eq!(
            count(&node, SyntaxKind::Missing),
            0,
            "{source:?}\n{node:#?}"
        );
        assert_eq!(
            pending_token_leading(exit, kind, spelling, LineEntry::InLine),
            []
        );
    }
}

#[test]
fn impl_body_recovery_is_bounded_and_keeps_terminal_boundaries_pending() {
    for source in [
        "impl T @ ;",
        "impl T: D @ : my x = y",
        "impl T:\n  @\n  my x = y",
    ] {
        let (green, _, remainder) = run_impl_declaration(source, 0, 0, LineEntry::InLine, None);
        assert_eq!(green.to_string(), source, "{source:?}");
        assert_eq!(remainder, "", "{source:?}");
        let node = declaration(&green);
        assert_eq!(count(&node, SyntaxKind::Error), 1, "{source:?}\n{node:#?}");
        assert_eq!(
            count(&node, SyntaxKind::Missing),
            0,
            "{source:?}\n{node:#?}"
        );
    }
    for (source, owned) in [
        ("impl T @   ", "impl T @"),
        ("impl T: D: @   ", "impl T: D: @"),
    ] {
        let (green, exit, remainder) = run_impl_declaration(source, 0, 0, LineEntry::InLine, None);
        // Terminal leading stays with the pending EOF Item, outside Error.
        assert_eq!(green.to_string(), owned, "{source:?}");
        let mut item = pending_item(exit, LineEntry::InLine);
        assert_eq!(emit_pending_leading_text(&mut item), "   ");
        assert_eq!(remainder, "", "{source:?}");
        assert_eq!(count(&declaration(&green), SyntaxKind::Error), 1);
    }
    for source in ["impl T", "impl T: D"] {
        let (green, _, remainder) = run_impl_declaration(source, 0, 0, LineEntry::InLine, None);
        assert_eq!(green.to_string(), source, "{source:?}");
        assert_eq!(remainder, "", "{source:?}");
        let node = declaration(&green);
        assert_eq!(
            count(&node, SyntaxKind::Missing),
            1,
            "{source:?}\n{node:#?}"
        );
        assert_eq!(count(&node, SyntaxKind::Error), 0, "{source:?}\n{node:#?}");
    }
    let source = "impl T { my x = y";
    let (green, _, remainder) = run_impl_declaration(source, 0, 0, LineEntry::InLine, None);
    assert_eq!(green.to_string(), source);
    assert_eq!(remainder, "");
    assert_eq!(count(&declaration(&green), SyntaxKind::Missing), 1);
    let source = "impl T: D: ;";
    let (green, exit, remainder) = run_impl_declaration(source, 0, 0, LineEntry::InLine, None);
    assert_eq!(green.to_string(), "impl T: D:");
    assert_eq!(remainder, "");
    assert_eq!(count(&declaration(&green), SyntaxKind::Missing), 1);
    assert_eq!(
        pending_token_leading(exit, TokenKind::Semicolon, ";", LineEntry::InLine),
        [(SyntaxKind::Whitespace, " ".to_owned())]
    );
    let source = "impl T:\nnext";
    let (green, exit, remainder) = run_impl_declaration(source, 0, 0, LineEntry::InLine, None);
    assert_eq!(green.to_string(), "impl T:");
    assert_eq!(remainder, "");
    assert_eq!(count(&declaration(&green), SyntaxKind::Missing), 1);
    assert_eq!(
        pending_tokens(exit, "next", LineEntry::InLine),
        [
            (SyntaxKind::Newline, "\n".to_owned()),
            (SyntaxKind::Identifier, "next".to_owned())
        ]
    );
}

#[test]
fn impl_braced_completion_hands_off_exactly_one_successor() {
    for (source, next, remainder) in [
        ("impl T {} next", "next", ""),
        ("impl T {}\nnext", "next", ""),
        ("impl T {} derives Eq", "derives", " Eq"),
    ] {
        let (green, exit, actual_remainder) =
            run_impl_declaration(source, 0, 0, LineEntry::InLine, None);
        assert_eq!(green.to_string(), "impl T {}", "{source:?}");
        assert_eq!(actual_remainder, remainder, "{source:?}");
        let pending = pending_tokens(exit, next, LineEntry::InLine);
        assert_eq!(pending.last().map(|(_, text)| text.as_str()), Some(next));
    }
}

#[test]
fn impl_preserves_caller_shallow_and_fenced_boundaries_with_origin() {
    let (green, exit, _) = run_impl_declaration(
        "impl T else",
        crate::lexical::stops::STOP_ELSE,
        1_200,
        LineEntry::InLine,
        None,
    );
    assert_eq!(green.to_string(), "impl T");
    assert_eq!(count(&declaration(&green), SyntaxKind::Missing), 1);
    assert_eq!(
        pending_tokens(exit, "else", LineEntry::InLine),
        [
            (SyntaxKind::Whitespace, " ".to_owned()),
            (SyntaxKind::Identifier, "else".to_owned())
        ]
    );
    let (green, exit, _) = run_impl_declaration("impl\n;", 0, 4_000, LineEntry::InLine, None);
    assert_eq!(green.to_string(), "impl");
    assert_eq!(count(&declaration(&green), SyntaxKind::Missing), 1);
    assert_eq!(
        pending_token_leading(exit, TokenKind::Semicolon, ";", LineEntry::InLine),
        [(SyntaxKind::Newline, "\n".to_owned())]
    );

    use crate::lexical::item::{BorrowedTarget, Boundary, StopKind};
    use crate::lexical::yumark::{FenceOpener, FencePrefixPolicy, QuoteTransitionKind};
    let fence = FenceBoundary {
        opener: FenceOpener {
            line: 0,
            marker: 0..3,
            marker_width: 3,
        },
        prefix_policy: FencePrefixPolicy::ActivePrefixQuote { depth: 2, base: 0 },
        close_column: 0,
    };
    let origin = 9_700;
    let accepted = "> > impl T {}";
    let source = format!("{accepted}\r\n> > ```\r\nouter");
    let (green, exit, remainder) =
        run_impl_declaration(&source, 0, origin, LineEntry::PhysicalStart, Some(&fence));
    assert_eq!(green.to_string(), accepted);
    assert_eq!(remainder, "> > ```\r\nouter");
    let Some(NormalizedExit::Complete(Err(Either::Left(boundary)), LineEntry::PhysicalStart)) =
        exit
    else {
        panic!("Impl must preserve the fenced terminal Item")
    };
    let (leading, pending) = emit_terminal_leading_text(boundary);
    assert_eq!(leading, "\r\n");
    assert_eq!(pending.coordinate(), origin + accepted.len() + 2);
    assert!(matches!(
        pending.into_kind(),
        Boundary::BorrowedClose(BorrowedTarget::YumarkFence(_))
    ));

    let accepted = "> > impl T:";
    let source = format!("{accepted}\r\n> > ```\r\nouter");
    let (green, exit, remainder) =
        run_impl_declaration(&source, 0, origin, LineEntry::PhysicalStart, Some(&fence));
    assert_eq!(green.to_string(), accepted);
    assert_eq!(remainder, "> > ```\r\nouter");
    let node = declaration(&green);
    assert_eq!(count(&node, SyntaxKind::ImplDescription), 0, "{node:#?}");
    assert_eq!(count(&node, SyntaxKind::Missing), 1, "{node:#?}");
    let Some(NormalizedExit::Complete(Err(Either::Left(boundary)), LineEntry::PhysicalStart)) =
        exit
    else {
        panic!("Impl body colon must preserve the fenced terminal Item")
    };
    let (leading, pending) = emit_terminal_leading_text(boundary);
    assert_eq!(leading, "\r\n");
    assert_eq!(pending.coordinate(), origin + accepted.len() + 2);
    assert!(matches!(
        pending.into_kind(),
        Boundary::BorrowedClose(BorrowedTarget::YumarkFence(_))
    ));

    let accepted = "> > impl T:";
    let source = format!("{accepted}\r\n> outer");
    let (green, exit, remainder) =
        run_impl_declaration(&source, 0, origin, LineEntry::PhysicalStart, Some(&fence));
    assert_eq!(green.to_string(), accepted);
    assert_eq!(remainder, "> outer");
    let node = declaration(&green);
    assert_eq!(count(&node, SyntaxKind::ImplDescription), 0, "{node:#?}");
    assert_eq!(count(&node, SyntaxKind::Missing), 1, "{node:#?}");
    let Some(NormalizedExit::Complete(Err(Either::Left(boundary)), LineEntry::PhysicalStart)) =
        exit
    else {
        panic!("Impl body colon must preserve the fenced transition Item")
    };
    let (leading, pending) = emit_terminal_leading_text(boundary);
    assert_eq!(leading, "\r\n");
    assert_eq!(pending.coordinate(), origin + accepted.len() + 2);
    assert!(matches!(
        pending.into_kind(),
        Boundary::Stop(StopKind::YumarkFence(transition))
            if transition.kind == QuoteTransitionKind::Reduced
    ));

    let source = format!("{accepted}\r\n> > ");
    let (green, exit, remainder) =
        run_impl_declaration(&source, 0, origin, LineEntry::PhysicalStart, Some(&fence));
    assert_eq!(green.to_string(), accepted);
    assert_eq!(remainder, "");
    let node = declaration(&green);
    assert_eq!(count(&node, SyntaxKind::ImplDescription), 0, "{node:#?}");
    assert_eq!(count(&node, SyntaxKind::Missing), 1, "{node:#?}");
    let Some(NormalizedExit::Complete(Err(Either::Left(boundary)), LineEntry::InLine)) = exit
    else {
        panic!("Impl body colon must preserve the fenced physical-EOF Item")
    };
    let (leading, pending) = emit_terminal_leading_text(boundary);
    assert_eq!(leading, "\r\n> > ");
    assert_eq!(pending.coordinate(), origin + source.len());
    assert_eq!(pending.into_kind(), Boundary::EofAfterTrivia);

    let source = format!("{accepted}/* open\r\n> > body");
    let (green, exit, remainder) =
        run_impl_declaration(&source, 0, origin, LineEntry::PhysicalStart, Some(&fence));
    assert_eq!(green.to_string(), accepted);
    assert_eq!(remainder, "");
    let node = declaration(&green);
    assert_eq!(count(&node, SyntaxKind::ImplDescription), 0, "{node:#?}");
    assert_eq!(count(&node, SyntaxKind::Missing), 1, "{node:#?}");
    let Some(NormalizedExit::Complete(Err(Either::Left(boundary)), LineEntry::InLine)) = exit
    else {
        panic!("Impl body colon must preserve the unterminated-comment EOF Item")
    };
    let (leading, pending) = emit_terminal_leading_text(boundary);
    assert_eq!(leading, "/* open\r\n> > body");
    assert_eq!(pending.coordinate(), origin + source.len());
    assert_eq!(pending.into_kind(), Boundary::EofAfterTrivia);

    let source = "impl T:\r\n  my x = y";
    let (green, _, remainder) = run_impl_declaration(source, 0, 0, LineEntry::InLine, None);
    assert_eq!(green.to_string(), source);
    assert_eq!(remainder, "");
    let node = declaration(&green);
    assert_eq!(count(&node, SyntaxKind::ImplDescription), 0, "{node:#?}");
    assert_eq!(count(&node, SyntaxKind::IndentedStatementBlock), 1);
}

#[test]
fn impl_private_owner_has_no_act_features_and_uses_canonical_statement_dispatch() {
    for source in ["impl T derives D;", "impl T with {}"] {
        let (green, _, _) = run_impl_declaration(source, 0, 0, LineEntry::InLine, None);
        let node = declaration(&green);
        assert_eq!(count(&node, SyntaxKind::DerivesClause), 0, "{source:?}");
        assert_eq!(
            count(&node, SyntaxKind::DeclarationCompanion),
            0,
            "{source:?}"
        );
    }
    let (green, _, remainder) =
        run_impl_declaration("impl T = Source;", 0, 0, LineEntry::InLine, None);
    assert_eq!(green.to_string(), "impl T = Source;");
    assert_eq!(remainder, "");
    assert_eq!(count(&declaration(&green), SyntaxKind::Error), 1);
    let (green, _) = run_statement("impl T;");
    assert_eq!(green.to_string(), "impl T;");
    assert_eq!(
        count(&SyntaxNode::new_root(green), SyntaxKind::ImplDeclaration),
        1
    );
}
