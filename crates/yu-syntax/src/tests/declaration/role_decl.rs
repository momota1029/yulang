use crate::{structural_diagnostic::StructuralKind, tests::support::*};

#[test]
fn role_schema_completed_head_statement_shell_composition() {
    use SyntaxKind::*;

    for (source, suffix, owned_end, missing_count, error_count) in [
        ("role T;", vec![(Semicolon, false, 6..7, ";")], 7, 0, 0),
        (
            "role T {}",
            vec![
                (Whitespace, false, 6..7, " "),
                (BracedStatementBlockExpression, true, 7..9, "{}"),
            ],
            9,
            0,
            0,
        ),
        (
            "role T: x",
            vec![(Colon, false, 6..7, ":"), (Statement, true, 7..9, " x")],
            9,
            0,
            0,
        ),
        (
            "role T  ",
            vec![(Whitespace, false, 6..8, "  "), (Missing, true, 8..8, "")],
            8,
            1,
            0,
        ),
        (
            "role T @  ",
            vec![(Whitespace, false, 6..7, " "), (Error, false, 7..8, "@")],
            8,
            0,
            1,
        ),
        (
            "role T @ ;",
            vec![
                (Whitespace, false, 6..7, " "),
                (Error, false, 7..8, "@"),
                (Whitespace, false, 8..9, " "),
                (Semicolon, false, 9..10, ";"),
            ],
            10,
            0,
            1,
        ),
        (
            "role T:  ",
            vec![(Colon, false, 6..7, ":"), (Missing, true, 7..7, "")],
            7,
            1,
            0,
        ),
        (
            "role T: @  ",
            vec![
                (Colon, false, 6..7, ":"),
                (Whitespace, false, 7..8, " "),
                (Error, false, 8..9, "@"),
            ],
            9,
            0,
            1,
        ),
        (
            "role T: @ x;",
            vec![
                (Colon, false, 6..7, ":"),
                (Whitespace, false, 7..8, " "),
                (Error, false, 8..9, "@"),
                (Statement, true, 9..11, " x"),
                (Semicolon, false, 11..12, ";"),
            ],
            12,
            0,
            1,
        ),
    ] {
        let (green, exit) = run_statement(source);
        let root = SyntaxNode::new_root(green);
        assert_eq!(root.kind(), Root, "{source:?}");
        assert!(root.parent().is_none());
        assert_eq!(root.to_string(), source);
        assert_eq!(
            root.text_range(),
            rowan::TextRange::new(0.into(), (source.len() as u32).into())
        );
        let root_children = root.children_with_tokens().collect::<Vec<_>>();
        let has_suffix = owned_end < source.len() as u32;
        assert_eq!(
            root_children.len(),
            1 + usize::from(has_suffix),
            "{source:?}"
        );
        let statement = root_children[0].as_node().expect("Statement node");
        assert_eq!(statement.kind(), Statement);
        assert_eq!(statement.parent(), Some(root.clone()));
        let owned_range = rowan::TextRange::new(0.into(), owned_end.into());
        assert_eq!(statement.text_range(), owned_range);
        assert_eq!(statement.to_string(), &source[..owned_end as usize]);
        let statement_children = statement.children_with_tokens().collect::<Vec<_>>();
        assert_eq!(statement_children.len(), 1);
        let role = statement_children[0]
            .as_node()
            .expect("RoleDeclaration node");
        assert_eq!(role.kind(), RoleDeclaration);
        assert_eq!(role.parent(), Some(statement.clone()));
        assert_eq!(role.text_range(), owned_range);
        assert_eq!(role.to_string(), &source[..owned_end as usize]);
        if has_suffix {
            let trailing = &root_children[1];
            assert!(trailing.as_token().is_some());
            assert_eq!(trailing.kind(), Whitespace);
            assert_eq!(trailing.parent(), Some(root.clone()));
            assert_eq!(
                trailing.text_range(),
                rowan::TextRange::new(owned_end.into(), (source.len() as u32).into())
            );
            assert_eq!(trailing.to_string(), &source[owned_end as usize..]);
        }

        let mut expected = vec![
            (RoleKw, false, 0..4, "role"),
            (Whitespace, false, 4..5, " "),
            (TypeExpression, true, 5..6, "T"),
        ];
        expected.extend(suffix);
        let children = role.children_with_tokens().collect::<Vec<_>>();
        assert_eq!(children.len(), expected.len(), "{source:?}");
        for (child, (kind, node, range, text)) in children.iter().zip(expected) {
            assert_eq!(child.parent(), Some(role.clone()));
            assert_eq!(child.kind(), kind, "{source:?}");
            assert_eq!(child.as_node().is_some(), node);
            assert_eq!(
                child.text_range(),
                rowan::TextRange::new(range.start.into(), range.end.into())
            );
            assert_eq!(child.to_string(), text);
            if kind == Missing {
                assert_eq!(child.as_node().unwrap().children_with_tokens().count(), 0);
            }
            if kind == Statement {
                let inline = child.as_node().unwrap();
                let leading = inline.first_token().expect("inline leading");
                assert_eq!(leading.kind(), Whitespace);
                let identifier = leading.parent().expect("inline IdentifierExpression");
                assert_eq!(identifier.kind(), IdentifierExpression);
                assert_ne!(identifier, *role);
                assert_ne!(identifier, *inline);
                let chain = identifier.parent().expect("inline OperatorChain");
                assert_eq!(chain.kind(), OperatorChain);
                assert_eq!(chain.parent(), Some(inline.clone()));
                assert_eq!(
                    leading.text_range(),
                    rowan::TextRange::new(range.start.into(), (range.start + 1).into())
                );
                assert_eq!(leading.to_string(), " ");
            }
        }
        for (kind, expected_count) in [(Missing, missing_count), (Error, error_count), (Invalid, 0)]
        {
            assert_eq!(
                root.descendants_with_tokens()
                    .filter(|child| child.kind() == kind)
                    .count(),
                expected_count,
                "{source:?}: {kind:?}"
            );
        }
        // The statement harness emits pending EOF leading after closing Statement.
        let Some(Err(Either::Right(mut end))) = exit else {
            panic!("{source:?}: expected EOF termination");
        };
        assert!(end.item.payload_view().is_eof());
        assert_eq!(emit_pending_leading_text(&mut end.item), "");
    }
}

// Slot evidence reads only ordered Rowan children and UTF-8 byte ranges.
fn assert_role_shell(source: &str, expected: &[(SyntaxKind, std::ops::Range<u32>)]) -> SyntaxNode {
    let (green, _, _) = run_role_declaration(source, 0, 0, LineEntry::InLine, None);
    let role = declaration(&green);
    let actual = role
        .children_with_tokens()
        .map(|child| {
            assert_eq!(child.parent(), Some(role.clone()));
            let range = child.text_range();
            (
                child.kind(),
                u32::from(range.start())..u32::from(range.end()),
            )
        })
        .collect::<Vec<_>>();
    assert_eq!(actual, expected, "{source:?}");
    assert!(
        !role
            .descendants()
            .any(|node| node.kind() == SyntaxKind::Invalid)
    );
    role
}

#[test]
fn role_schema_completed_head_selects_body_introducer() {
    use SyntaxKind::*;
    for (source, suffix) in [
        ("role 型;", vec![(Semicolon, 8..9)]),
        (
            "role 型 {}",
            vec![(Whitespace, 8..9), (BracedStatementBlockExpression, 9..11)],
        ),
        ("role 型: x", vec![(Colon, 8..9), (Statement, 9..11)]),
        ("role 型  ", vec![(Whitespace, 8..10), (Missing, 10..10)]),
        ("role 型  )", vec![(Missing, 8..8)]),
        ("role 型 @  ", vec![(Whitespace, 8..9), (Error, 9..10)]),
        ("role 型 @  )", vec![(Whitespace, 8..9), (Error, 9..10)]),
        (
            "role 型 @  ~   ;",
            vec![
                (Whitespace, 8..9),
                (Error, 9..10),
                (Error, 10..12),
                (Error, 12..13),
                (Whitespace, 13..16),
                (Semicolon, 16..17),
            ],
        ),
        (
            "role 型 @ {}",
            vec![
                (Whitespace, 8..9),
                (Error, 9..10),
                (Whitespace, 10..11),
                (BracedStatementBlockExpression, 11..13),
            ],
        ),
        (
            "role 型 @ : x",
            vec![
                (Whitespace, 8..9),
                (Error, 9..10),
                (Whitespace, 10..11),
                (Colon, 11..12),
                (Statement, 12..14),
            ],
        ),
    ] {
        let mut expected = vec![(RoleKw, 0..4), (Whitespace, 4..5), (TypeExpression, 5..8)];
        expected.extend(suffix);
        assert_role_shell(source, &expected);
    }
}

#[test]
fn role_schema_actual_colon_selects_inline_body() {
    use SyntaxKind::*;
    for (source, suffix) in [
        ("role 型:   ", vec![(Missing, 9..9)]),
        ("role 型:  ;", vec![(Missing, 9..9)]),
        ("role 型:\r\nnext", vec![(Missing, 9..9)]),
        ("role 型: @  ", vec![(Whitespace, 9..10), (Error, 10..11)]),
        ("role 型: @  ;", vec![(Whitespace, 9..10), (Error, 10..11)]),
        (
            "role 型: @  ~   x;",
            vec![
                (Whitespace, 9..10),
                (Error, 10..11),
                (Error, 11..13),
                (Error, 13..14),
                (Statement, 14..18),
                (Semicolon, 18..19),
            ],
        ),
    ] {
        let mut expected = vec![
            (RoleKw, 0..4),
            (Whitespace, 4..5),
            (TypeExpression, 5..8),
            (Colon, 8..9),
        ];
        expected.extend(suffix);
        let role = assert_role_shell(source, &expected);
        if let Some(statement) = role.children().find(|node| node.kind() == Statement) {
            let leading = statement.first_token().expect("retry leading");
            assert_eq!(leading.kind(), Whitespace);
            assert_eq!(
                leading.text_range(),
                rowan::TextRange::new(14.into(), 17.into())
            );
        }
    }
}

#[test]
fn role_schema_incomplete_head_does_not_select_body_introducer() {
    use SyntaxKind::*;
    // Missing Head has a TypeExpression wrapper; malformed Head can precede
    // one. Neither is the slot following a completed Head.
    for (source, suffix) in [
        ("role )", vec![(TypeExpression, 5..5)]),
        ("role ;", vec![(TypeExpression, 5..5), (Semicolon, 5..6)]),
        ("role @ ;", vec![(Error, 5..6)]),
        (
            "role @ 型;",
            vec![(Error, 5..6), (TypeExpression, 6..10), (Semicolon, 10..11)],
        ),
    ] {
        let mut expected = vec![(RoleKw, 0..4), (Whitespace, 4..5)];
        expected.extend(suffix);
        let role = assert_role_shell(source, &expected);
        for head in role
            .children()
            .filter(|node| node.kind() == TypeExpression && node.text_range().is_empty())
        {
            let children = head.children_with_tokens().collect::<Vec<_>>();
            assert_eq!(children.len(), 1);
            assert_eq!(children[0].kind(), Missing);
            assert_eq!(children[0].parent(), Some(head.clone()));
            assert_eq!(children[0].text_range(), head.text_range());
        }
    }
}

#[test]
fn role_schema_required_head_has_complete_ordered_evidence() {
    use SyntaxKind::*;

    for (source, suffix, owned, recovery_end) in [
        (
            "role ;",
            vec![
                (TypeExpression, true, 5..5, ""),
                (Semicolon, false, 5..6, ";"),
            ],
            "role ;",
            Some(5),
        ),
        (
            "role @ ;",
            vec![(Error, false, 5..6, "@")],
            "role @",
            Some(6),
        ),
        (
            "role @ T;",
            vec![
                (Error, false, 5..6, "@"),
                (TypeExpression, true, 6..8, " T"),
                (Semicolon, false, 8..9, ";"),
            ],
            "role @ T;",
            Some(6),
        ),
        (
            "role T;",
            vec![
                (TypeExpression, true, 5..6, "T"),
                (Semicolon, false, 6..7, ";"),
            ],
            "role T;",
            None,
        ),
        (
            "role @  ~   型;",
            vec![
                (Error, false, 5..6, "@"),
                (Error, false, 6..8, "  "),
                (Error, false, 8..9, "~"),
                (TypeExpression, true, 9..15, "   型"),
                (Semicolon, false, 15..16, ";"),
            ],
            "role @  ~   型;",
            Some(9),
        ),
    ] {
        let (green, exit, facts, remainder) = typed_role(source, 0, None);
        assert_eq!(green.to_string(), owned, "{source:?}");
        assert_eq!(remainder, "", "{source:?}");
        let (canonical, _, canonical_remainder) =
            run_statement_normalized(source, 100, LineEntry::InLine, None);
        assert_eq!(canonical_remainder, "");
        let role = declaration(&canonical);
        assert_eq!(role.green(), declaration(&green).green());
        let statement = role.parent().expect("Role parent");
        assert_eq!(statement.kind(), Statement);
        let root = statement.parent().expect("Statement parent");
        assert_eq!(root.kind(), Root);
        assert!(root.parent().is_none());
        assert_eq!(root.to_string(), owned);
        assert_eq!(statement.to_string(), owned);
        assert_eq!(role.to_string(), owned);
        assert!(
            !root
                .descendants_with_tokens()
                .any(|child| child.kind() == Invalid)
        );
        let children = role.children_with_tokens().collect::<Vec<_>>();
        let mut expected = vec![
            (RoleKw, false, 0..4, "role"),
            (Whitespace, false, 4..5, " "),
        ];
        expected.extend(suffix);
        assert_eq!(children.len(), expected.len(), "{source:?}");
        for (child, (kind, node, range, text)) in children.iter().zip(expected) {
            assert_eq!(child.parent(), Some(role.clone()));
            assert_eq!(child.kind(), kind);
            assert_eq!(child.as_node().is_some(), node);
            assert_eq!(
                child.text_range(),
                rowan::TextRange::new(range.start.into(), range.end.into())
            );
            assert_eq!(child.to_string(), text);
        }

        // The Head slot starts after keyword trivia and ends at its first
        // completed TypeExpression. No recovery ledger selects this slot.
        let head = children[2..].iter().find_map(|child| child.as_node());
        let errors = children[2..]
            .iter()
            .take_while(|child| child.kind() == Error)
            .collect::<Vec<_>>();
        assert_eq!(
            errors.len(),
            if source.contains('~') {
                3
            } else {
                usize::from(source.contains('@'))
            }
        );
        for pair in errors.windows(2) {
            assert_eq!(pair[0].text_range().end(), pair[1].text_range().start());
        }
        assert_eq!(
            root.descendants_with_tokens()
                .filter(|child| child.kind() == Error)
                .count(),
            errors.len()
        );
        if !errors.is_empty() {
            // Select the malformed mandatory Type slot from its complete
            // ordered Role ancestry, before consulting compatibility records.
            assert_eq!(root.children_with_tokens().count(), 1);
            assert_eq!(statement.children_with_tokens().count(), 1);
            assert_eq!(role.kind(), RoleDeclaration);
            let malformed = match children.as_slice() {
                [keyword, trivia, suffix @ ..]
                    if keyword.as_token().is_some()
                        && keyword.kind() == RoleKw
                        && keyword.text_range() == rowan::TextRange::new(0.into(), 4.into())
                        && trivia.as_token().is_some()
                        && trivia.kind() == Whitespace
                        && trivia.text_range() == rowan::TextRange::new(4.into(), 5.into()) =>
                {
                    suffix
                }
                _ => panic!("Type Primary Error requires the ordered Role prefix"),
            };
            let group = malformed
                .iter()
                .take_while(|child| child.kind() == Error)
                .collect::<Vec<_>>();
            assert_eq!(
                group,
                children
                    .iter()
                    .filter(|child| child.kind() == Error)
                    .collect::<Vec<_>>()
            );
            assert!(group.iter().all(|child| child.as_token().is_some()));
            let range = rowan::TextRange::new(
                group.first().unwrap().text_range().start(),
                group.last().unwrap().text_range().end(),
            );
            let expected_end = match group.as_slice() {
                [one] => {
                    assert_eq!(one.text_range(), rowan::TextRange::new(5.into(), 6.into()));
                    6
                }
                [first, leading, last] => {
                    assert_eq!(
                        first.text_range(),
                        rowan::TextRange::new(5.into(), 6.into())
                    );
                    assert_eq!(
                        leading.text_range(),
                        rowan::TextRange::new(6.into(), 8.into())
                    );
                    assert_eq!(last.text_range(), rowan::TextRange::new(8.into(), 9.into()));
                    9
                }
                _ => panic!("unexpected direct Type Primary Error group"),
            };
            assert_eq!(range, rowan::TextRange::new(5.into(), expected_end.into()));
            assert!(
                !root
                    .descendants_with_tokens()
                    .any(|child| child.kind() == Missing)
            );
            match &malformed[group.len()..] {
                [] => {
                    assert_eq!(range.end(), rowan::TextSize::from(6));
                    assert_eq!(role.text_range(), rowan::TextRange::new(0.into(), 6.into()));
                }
                [retry, semicolon] => {
                    let retry = retry.as_node().expect("retry TypeExpression node");
                    assert_eq!(retry.kind(), TypeExpression);
                    assert_eq!(retry.text_range().start(), range.end());
                    let retry_children = retry.children_with_tokens().collect::<Vec<_>>();
                    let [leading, identifier] = retry_children.as_slice() else {
                        panic!("retry owns exactly native leading and Identifier");
                    };
                    assert!(leading.as_token().is_some());
                    assert_eq!(leading.kind(), Whitespace);
                    assert_eq!(leading.text_range().start(), range.end());
                    assert!(identifier.as_token().is_some());
                    assert_eq!(identifier.kind(), Identifier);
                    assert_eq!(leading.text_range().end(), identifier.text_range().start());
                    assert_eq!(identifier.text_range().end(), retry.text_range().end());
                    assert!(semicolon.as_token().is_some());
                    assert_eq!(semicolon.kind(), Semicolon);
                    assert_eq!(semicolon.text_range().start(), retry.text_range().end());
                    assert_eq!(semicolon.text_range().end(), role.text_range().end());
                }
                _ => panic!("malformed Head ends or retries through TypeExpression and semicolon"),
            }
        }
        if let Some(head) = head {
            assert_eq!(head.kind(), TypeExpression);
            if head.text_range().is_empty() {
                let missing = head.children_with_tokens().collect::<Vec<_>>();
                assert_eq!(missing.len(), 1);
                assert!(missing[0].as_node().is_some());
                assert_eq!(missing[0].kind(), Missing);
                assert_eq!(missing[0].parent(), Some(head.clone()));
                assert_eq!(missing[0].text_range(), rowan::TextRange::empty(5.into()));
                assert_eq!(missing[0].to_string(), "");
                assert_eq!(
                    missing[0].as_node().unwrap().children_with_tokens().count(),
                    0
                );
                let missing_ranges = match children.as_slice() {
                    [keyword, trivia, type_expression, semicolon]
                        if role.kind() == RoleDeclaration
                            && keyword.kind() == RoleKw
                            && trivia.kind() == Whitespace
                            && type_expression.as_node() == Some(head)
                            && semicolon.kind() == Semicolon =>
                    {
                        missing
                            .iter()
                            .filter(|child| child.kind() == Missing)
                            .map(|child| child.text_range())
                            .collect::<Vec<_>>()
                    }
                    _ => panic!("fresh Head Missing requires the ordered Role shell"),
                };
                assert_eq!(missing_ranges, vec![rowan::TextRange::empty(5.into())]);
            } else if let Some(last) = errors.last() {
                assert_eq!(last.text_range().end(), head.text_range().start());
                let leading = head.first_child_or_token().expect("native retry leading");
                assert!(leading.as_token().is_some());
                assert_eq!(leading.kind(), Whitespace);
                assert_eq!(leading.parent(), Some(head.clone()));
                let (start, end, text) = if source.contains('~') {
                    (9, 12, "   ")
                } else {
                    (6, 7, " ")
                };
                assert_eq!(
                    leading.text_range(),
                    rowan::TextRange::new(start.into(), end.into())
                );
                assert_eq!(leading.to_string(), text);
            }
        }
        assert_eq!(
            root.descendants()
                .filter(|node| node.kind() == Missing)
                .count(),
            usize::from(source == "role ;")
        );
        if source == "role @ ;" {
            assert_eq!(
                pending_token_leading(exit, TokenKind::Semicolon, ";", LineEntry::InLine),
                vec![(Whitespace, " ".to_owned())]
            );
        } else {
            let mut item = pending_item(exit, LineEntry::InLine);
            assert!(item.payload_view().is_eof());
            assert_eq!(emit_pending_leading_text(&mut item), "");
        }

        let expected_facts = recovery_end
            .map(|end| {
                if end == 5 {
                    (StructuralKind::Missing, 5..5)
                } else {
                    (StructuralKind::ErrorGroup, 5..end)
                }
            })
            .into_iter()
            .collect::<Vec<_>>();
        assert_eq!(facts, expected_facts, "{source:?}");
    }
}

#[test]
fn role_schema_inline_binding_recovery_remains_in_child_body() {
    use SyntaxKind::*;
    let role = assert_role_shell(
        "role 型: my x =",
        &[
            (RoleKw, 0..4),
            (Whitespace, 4..5),
            (TypeExpression, 5..8),
            (Colon, 8..9),
            (Statement, 9..16),
        ],
    );
    let statement = role
        .children()
        .find(|node| node.kind() == Statement)
        .unwrap();
    let binding = statement
        .children()
        .find(|node| node.kind() == BindingStatement)
        .unwrap();
    let body = binding
        .children()
        .find(|node| node.kind() == BindingBody)
        .unwrap();
    let missing = body.children().find(|node| node.kind() == Missing).unwrap();
    assert_eq!(missing.parent(), Some(body));
    assert_eq!(missing.text_range(), rowan::TextRange::empty(16.into()));
}

fn typed_role<'s>(
    source: &'s str,
    stops: Stops,
    fence: Option<&FenceBoundary>,
) -> (
    GreenNode,
    Option<NormalizedExit>,
    Vec<StructuralFact>,
    &'s str,
) {
    let operators = OperatorTable::empty();
    let mut input = source;
    let mut recover = Recover::new_for_test(&operators);
    let mut builder = GreenNodeBuilder::new();
    builder.start_node(SyntaxKind::Root.into());
    let exit = role_declaration_witness(
        crate::cursor::SyntaxIn::new(&mut input, &mut recover, &mut builder),
        0,
        stops,
        crate::statement::StatementLineHandoff::OrdinaryLayout,
        100,
        LineEntry::InLine,
        fence,
    );
    builder.finish_node();
    let green = finish_with_discarded_recoveries(builder, recover);
    let facts = structural_facts(&green);
    (green, exit, facts, input)
}

#[test]
fn role_body_structural_facts_are_exact_with_leading_ownership() {
    for (source, kind, range, owned, leading) in [
        ("role R   ", StructuralKind::Missing, 9..9, "role R   ", ""),
        ("role R  )", StructuralKind::Missing, 6..6, "role R", "  "),
        (
            "role R @  ~   ;",
            StructuralKind::ErrorGroup,
            7..11,
            "role R @  ~   ;",
            "",
        ),
        (
            "role R @ {}",
            StructuralKind::ErrorGroup,
            7..8,
            "role R @ {}",
            "",
        ),
        (
            "role R @ : x",
            StructuralKind::ErrorGroup,
            7..8,
            "role R @ : x",
            "",
        ),
        (
            "role R @   ",
            StructuralKind::ErrorGroup,
            7..8,
            "role R @",
            "   ",
        ),
        (
            "role R @  )",
            StructuralKind::ErrorGroup,
            7..8,
            "role R @",
            "  ",
        ),
        (
            "role R:   ",
            StructuralKind::Missing,
            7..7,
            "role R:",
            "   ",
        ),
        ("role R:  ;", StructuralKind::Missing, 7..7, "role R:", "  "),
        (
            "role R:\r\nnext",
            StructuralKind::Missing,
            7..7,
            "role R:",
            "\r\n",
        ),
        ("role R:  ]", StructuralKind::Missing, 7..7, "role R:", "  "),
        (
            "role R: @  ~   x",
            StructuralKind::ErrorGroup,
            8..12,
            "role R: @  ~   x",
            "",
        ),
        (
            "role R: @  ;",
            StructuralKind::ErrorGroup,
            8..9,
            "role R: @",
            "  ",
        ),
        (
            "role R: @   ",
            StructuralKind::ErrorGroup,
            8..9,
            "role R: @",
            "   ",
        ),
        (
            "role 型: @   ]",
            StructuralKind::ErrorGroup,
            10..11,
            "role 型: @",
            "   ",
        ),
    ] {
        let (green, exit, facts, _remainder) = typed_role(source, 0, None);
        assert_eq!(green.to_string(), owned, "{source:?}");
        let mut item = pending_item(exit, LineEntry::InLine);
        assert_eq!(emit_pending_leading_text(&mut item), leading, "{source:?}");
        assert_eq!(facts, [(kind, range)], "{source:?}");
    }
}

fn declaration(green: &GreenNode) -> SyntaxNode {
    SyntaxNode::new_root(green.clone())
        .descendants()
        .find(|node| node.kind() == SyntaxKind::RoleDeclaration)
        .expect("RoleDeclaration")
}

#[test]
fn role_body_protected_fence_and_contextual_stop_preserve_exact_handoff() {
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
    for (source, owned, fact) in [
        (
            "role R\r\n> > ```\r\nouter",
            "role R",
            (StructuralKind::Missing, 6..6),
        ),
        (
            "role R:\r\n> > ```\r\nouter",
            "role R:",
            (StructuralKind::Missing, 7..7),
        ),
        (
            "role R @\r\n> > ```\r\nouter",
            "role R @",
            (StructuralKind::ErrorGroup, 7..8),
        ),
        (
            "role R: @\r\n> > ```\r\nouter",
            "role R: @",
            (StructuralKind::ErrorGroup, 8..9),
        ),
    ] {
        let (green, exit, facts, remainder) = typed_role(source, 0, Some(&fence));
        assert_eq!(green.to_string(), owned);
        assert_eq!(facts, [fact]);
        let item = pending_item(exit, LineEntry::PhysicalStart);
        let (leading, boundary) = emit_terminal_leading_text(item);
        assert_eq!(leading, "\r\n");
        assert_eq!(boundary.coordinate(), 100 + owned.len() + 2);
        assert_eq!(remainder, "> > ```\r\nouter");
    }
    for (owned, fact) in [
        ("role R", (StructuralKind::Missing, 6..6)),
        ("role R:", (StructuralKind::Missing, 7..7)),
        ("role R @", (StructuralKind::ErrorGroup, 7..8)),
        ("role R: @", (StructuralKind::ErrorGroup, 8..9)),
    ] {
        let source = format!("{owned}  else suffix");
        let (green, exit, facts, remainder) = typed_role(&source, STOP_ELSE, None);
        assert_eq!(green.to_string(), owned);
        assert_eq!(facts, [fact]);
        assert_eq!(remainder, " suffix");
        let mut item = pending_item(exit, LineEntry::InLine);
        assert_eq!(emit_pending_leading_text(&mut item), "  ");
        assert_eq!(item.payload_view().spelling(), Some("else"));
    }
}

#[test]
fn role_body_recovery_retains_head_and_statement_child_owners() {
    for (source, fact, parent) in [
        (
            "role @ ;",
            (StructuralKind::ErrorGroup, 5..6),
            SyntaxKind::RoleDeclaration,
        ),
        (
            "role )",
            (StructuralKind::Missing, 5..5),
            SyntaxKind::TypeExpression,
        ),
    ] {
        let (green, _, facts, _) = typed_role(source, 0, None);
        assert_eq!(facts, [fact], "{source}");
        let occurrence = structural_diagnostics(&green).pop().expect("one fact");
        assert_eq!(occurrence.parent(), parent, "{source}");
    }
    for (source, range) in [
        ("role R: my x =", 14..14),
        ("role R {my x =}", 14..14),
        ("role R:\n  my x =", 16..16),
    ] {
        let (green, _, facts, _) = typed_role(source, 0, None);
        assert_eq!(facts, [(StructuralKind::Missing, range)], "{source}");
        let occurrence = structural_diagnostics(&green).pop().expect("one fact");
        assert_eq!(occurrence.parent(), SyntaxKind::BindingBody, "{source}");
    }
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
fn role_private_owner_builds_each_body_form_losslessly_with_flat_topology() {
    for (source, braced, indented) in [
        ("role Eq;", 0, 0),
        ("role Eq { my x = y }", 1, 0),
        ("role Eq: my x = y;", 0, 0),
        ("role Eq:\n  my x = y", 0, 1),
    ] {
        let (green, exit, remainder) = run_role_declaration(source, 0, 0, LineEntry::InLine, None);
        assert!(exit.is_some(), "{source:?}");
        assert_eq!(green.to_string(), source, "{source:?}");
        assert_eq!(remainder, "", "{source:?}");
        let node = declaration(&green);
        assert_eq!(
            node.children()
                .filter(|child| child.kind() == SyntaxKind::TypeExpression)
                .count(),
            1,
            "{source:?}"
        );
        assert_eq!(
            count(&node, SyntaxKind::Missing),
            0,
            "{source:?}\n{node:#?}"
        );
        assert_eq!(count(&node, SyntaxKind::Error), 0, "{source:?}\n{node:#?}");
        assert_eq!(
            count(&node, SyntaxKind::BracedStatementBlockExpression),
            braced
        );
        assert_eq!(count(&node, SyntaxKind::IndentedStatementBlock), indented);
        assert_eq!(count(&node, SyntaxKind::RoleDeclaration), 1);
        assert_eq!(token_count(&node, SyntaxKind::RoleKw), 1);
    }

    let (green, _, _) = run_role_declaration("role Eq;", 0, 0, LineEntry::InLine, None);
    let kinds: Vec<_> = declaration(&green)
        .children_with_tokens()
        .map(|element| element.kind())
        .collect();
    assert_eq!(
        kinds,
        [
            SyntaxKind::RoleKw,
            SyntaxKind::Whitespace,
            SyntaxKind::TypeExpression,
            SyntaxKind::Semicolon,
        ]
    );
}

#[test]
fn role_intro_is_exact_and_visibility_led_rejections_roll_back() {
    for source in ["role R;", "my role R;", "our role R;", "pub role R;"] {
        let (green, exit, _) = run_role_declaration(source, 0, 0, LineEntry::InLine, None);
        assert!(exit.is_some(), "{source:?}");
        assert_eq!(green.to_string(), source, "{source:?}");
        assert_eq!(token_count(&declaration(&green), SyntaxKind::RoleKw), 1);
    }

    for source in [
        "roles R;",
        "roleplay R;",
        "myrole R;",
        "my roleish R;",
        "pub roles R;",
        "our\nrole R;",
        "\nrole R;",
        "\nmy role R;",
    ] {
        let (green, exit, remainder) =
            run_role_declaration(source, 0, 700, LineEntry::InLine, None);
        assert!(exit.is_none(), "{source:?}");
        assert_eq!(green.to_string(), "", "{source:?}");
        assert_eq!(remainder, source, "{source:?}");
    }

    let (green, exit, _) = run_role_declaration("my role = value", 0, 0, LineEntry::InLine, None);
    assert!(exit.is_some());
    assert_eq!(token_count(&declaration(&green), SyntaxKind::RoleKw), 1);

    for source in ["\n  role R;", "pub\n  role\n    R;"] {
        let (green, exit, _) = run_role_declaration(source, 0, 0, LineEntry::InLine, None);
        assert!(exit.is_some(), "{source:?}");
        assert_eq!(green.to_string(), source, "{source:?}");
    }
}

#[test]
fn role_head_is_one_full_type_and_nested_body_punctuation_is_suspended() {
    for source in [
        "role F (A->B) 't;",
        "role F(A -> B) 't;",
        "role (:{A});",
        "role ({ value: T });",
        "role for 'a: ('a -> :{Some 'a});",
        "role '[io];",
        "role [io] Task;",
    ] {
        let (green, _, remainder) = run_role_declaration(source, 0, 0, LineEntry::InLine, None);
        assert_eq!(green.to_string(), source, "{source:?}");
        assert_eq!(remainder, "", "{source:?}");
        let node = declaration(&green);
        assert_eq!(
            node.children()
                .filter(|child| child.kind() == SyntaxKind::TypeExpression)
                .count(),
            1,
            "{source:?}"
        );
        assert_eq!(
            count(&node, SyntaxKind::Missing),
            0,
            "{source:?}\n{node:#?}"
        );
        assert_eq!(count(&node, SyntaxKind::Error), 0, "{source:?}\n{node:#?}");
    }

    let source = "role :{A};";
    let (green, _, remainder) = run_role_declaration(source, 0, 0, LineEntry::InLine, None);
    assert_eq!(green.to_string(), source);
    assert_eq!(remainder, "");
    let node = declaration(&green);
    assert_eq!(count(&node, SyntaxKind::PolymorphicVariantType), 1);
    assert_eq!(count(&node, SyntaxKind::Missing), 0, "{node:#?}");

    let (green, _, _) = run_role_declaration("role '[io];", 0, 0, LineEntry::InLine, None);
    assert_eq!(count(&declaration(&green), SyntaxKind::EffectRowType), 1);
    let (green, _, _) = run_role_declaration("role [io] Task;", 0, 0, LineEntry::InLine, None);
    assert_eq!(count(&declaration(&green), SyntaxKind::BracketRow), 1);
}

#[test]
fn role_head_retains_inherited_type_ml_stop_before_spaced_arrow() {
    let source = "role F (A -> B) 't;";
    let (green, _, remainder) = run_role_declaration(source, 0, 0, LineEntry::InLine, None);
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
fn role_head_missing_and_malformed_recovery_retries_without_cascade() {
    for (source, missing, errors, braced) in [
        ("role;", 1, 0, 0),
        ("role: my x = y", 1, 0, 0),
        ("role{}", 1, 0, 1),
        ("role @ Eq;", 0, 1, 0),
    ] {
        let (green, _, remainder) = run_role_declaration(source, 0, 0, LineEntry::InLine, None);
        assert_eq!(green.to_string(), source, "{source:?}");
        assert_eq!(remainder, "", "{source:?}");
        let node = declaration(&green);
        assert_eq!(
            count(&node, SyntaxKind::Missing),
            missing,
            "{source:?}\n{node:#?}"
        );
        assert_eq!(
            count(&node, SyntaxKind::Error),
            errors,
            "{source:?}\n{node:#?}"
        );
        assert_eq!(
            count(&node, SyntaxKind::BracedStatementBlockExpression),
            braced
        );
    }

    for source in ["role ;", "role {}", "role : my x = y"] {
        let (green, _, remainder) = run_role_declaration(source, 0, 0, LineEntry::InLine, None);
        assert_eq!(green.to_string(), source, "{source:?}");
        assert_eq!(remainder, "", "{source:?}");
        let node = declaration(&green);
        assert_eq!(
            count(&node, SyntaxKind::Missing),
            1,
            "{source:?}\n{node:#?}"
        );
        assert_eq!(count(&node, SyntaxKind::Error), 0, "{source:?}\n{node:#?}");
        let whitespace = node
            .children_with_tokens()
            .filter_map(|element| element.into_token())
            .find(|token| token.kind() == SyntaxKind::Whitespace)
            .expect("same-line head gap");
        let missing = node
            .descendants()
            .find(|child| child.kind() == SyntaxKind::Missing)
            .expect("missing Role head");
        assert_eq!(whitespace.text(), " ");
        assert_eq!(whitespace.text_range().end(), missing.text_range().start());
    }

    for (source, pending_kind, pending_spelling, remainder, spaced) in [
        ("role @;", TokenKind::Semicolon, ";", "", false),
        ("role @{}", TokenKind::LBrace, "{", "}", false),
        ("role @:", TokenKind::Colon, ":", "", false),
        ("role @ ;", TokenKind::Semicolon, ";", "", true),
        ("role @ {}", TokenKind::LBrace, "{", "}", true),
        ("role @ :", TokenKind::Colon, ":", "", true),
    ] {
        let (green, exit, actual_remainder) =
            run_role_declaration(source, 0, 0, LineEntry::InLine, None);
        assert_eq!(green.to_string(), "role @", "{source:?}");
        assert_eq!(actual_remainder, remainder, "{source:?}");
        let node = declaration(&green);
        assert_eq!(
            count(&node, SyntaxKind::Missing),
            0,
            "{source:?}\n{node:#?}"
        );
        assert_eq!(count(&node, SyntaxKind::Error), 1, "{source:?}\n{node:#?}");
        let error = crate::tests::recovery_output::recovery_groups(&node)
            .into_iter()
            .next()
            .expect("one malformed Type head run");
        assert_eq!(
            error.parent().map(|parent| parent.kind()),
            Some(SyntaxKind::RoleDeclaration),
            "{source:?}\n{node:#?}"
        );
        assert_eq!(
            pending_token_leading(exit, pending_kind, pending_spelling, LineEntry::InLine),
            if spaced {
                vec![(SyntaxKind::Whitespace, " ".to_owned())]
            } else {
                vec![]
            },
            "{source:?}"
        );
    }
}

#[test]
fn role_missing_head_commits_admitted_deeper_gap_before_missing() {
    for newline in ["\n", "\r\n"] {
        for body in [";", "{}", ": my x = y"] {
            let source = format!("role{newline}  {body}");
            let (green, _, remainder) =
                run_role_declaration(&source, 0, 0, LineEntry::InLine, None);
            assert_eq!(green.to_string(), source, "{source:?}");
            assert_eq!(remainder, "", "{source:?}");
            let node = declaration(&green);
            assert_eq!(
                count(&node, SyntaxKind::Missing),
                1,
                "{source:?}\n{node:#?}"
            );
            assert_eq!(count(&node, SyntaxKind::Error), 0, "{source:?}\n{node:#?}");
            let missing = node
                .descendants()
                .find(|child| child.kind() == SyntaxKind::Missing)
                .expect("missing Role head");
            assert_eq!(
                missing.parent().map(|parent| parent.kind()),
                Some(SyntaxKind::TypeExpression),
                "{source:?}\n{node:#?}"
            );
            let missing_start = missing.text_range().start();
            let committed_gap: Vec<_> = node
                .children_with_tokens()
                .filter_map(|element| element.into_token())
                .filter(|token| {
                    matches!(token.kind(), SyntaxKind::Newline | SyntaxKind::Whitespace)
                        && token.text_range().end() <= missing_start
                })
                .map(|token| (token.kind(), token.text().to_owned()))
                .collect();
            assert_eq!(
                committed_gap,
                [
                    (SyntaxKind::Newline, newline.to_owned()),
                    (SyntaxKind::Whitespace, "  ".to_owned()),
                ],
                "{source:?}\n{node:#?}"
            );
        }
    }
}

#[test]
fn role_missing_head_leaves_equal_depth_gap_with_body_starter_pending() {
    let source = "role\n;";
    let (green, exit, remainder) = run_role_declaration(source, 0, 0, LineEntry::InLine, None);
    assert_eq!(green.to_string(), "role");
    assert_eq!(remainder, "");
    let node = declaration(&green);
    assert_eq!(count(&node, SyntaxKind::Missing), 1, "{node:#?}");
    assert_eq!(count(&node, SyntaxKind::Error), 0, "{node:#?}");
    assert_eq!(
        pending_token_leading(exit, TokenKind::Semicolon, ";", LineEntry::InLine),
        [(SyntaxKind::Newline, "\n".to_owned())]
    );
}

#[test]
fn role_complete_head_requires_exactly_one_body_introducer() {
    let (green, exit, remainder) = run_role_declaration("role R", 0, 0, LineEntry::InLine, None);
    assert_eq!(green.to_string(), "role R");
    assert_eq!(remainder, "");
    let node = declaration(&green);
    assert_eq!(count(&node, SyntaxKind::Missing), 1, "{node:#?}");
    assert_eq!(count(&node, SyntaxKind::Error), 0, "{node:#?}");
    assert!(exit.is_some());

    let source = "role R\nnext";
    let (green, exit, remainder) = run_role_declaration(source, 0, 0, LineEntry::InLine, None);
    assert_eq!(green.to_string(), "role R");
    assert_eq!(remainder, "");
    assert_eq!(count(&declaration(&green), SyntaxKind::Missing), 1);
    assert_eq!(
        pending_tokens(exit, "next", LineEntry::InLine),
        [
            (SyntaxKind::Newline, "\n".to_owned()),
            (SyntaxKind::Identifier, "next".to_owned()),
        ]
    );
}

#[test]
fn role_isolated_body_recovery_commits_one_error_node_per_malformed_run() {
    for (source, errors) in [
        ("role R @ ;", 1),
        ("role R @ : my x = y", 1),
        ("role R: @ my x = y", 1),
    ] {
        let (green, _, remainder) = run_role_declaration(source, 0, 0, LineEntry::InLine, None);
        assert_eq!(green.to_string(), source, "{source:?}");
        assert_eq!(remainder, "", "{source:?}");
        let node = declaration(&green);
        assert_eq!(
            count(&node, SyntaxKind::Error),
            errors,
            "{source:?}\n{node:#?}"
        );
        assert_eq!(
            count(&node, SyntaxKind::Missing),
            0,
            "{source:?}\n{node:#?}"
        );
    }

    for (source, owned) in [("role R @   ", "role R @"), ("role R: @   ", "role R: @")] {
        let (green, exit, remainder) = run_role_declaration(source, 0, 0, LineEntry::InLine, None);
        // The Error ends before the pending EOF Item's leading.
        assert_eq!(green.to_string(), owned, "{source:?}");
        let mut pending = pending_item(exit, LineEntry::InLine);
        assert_eq!(emit_pending_leading_text(&mut pending), "   ");
        assert_eq!(remainder, "", "{source:?}");
        let node = declaration(&green);
        assert_eq!(count(&node, SyntaxKind::Error), 1, "{source:?}\n{node:#?}");
        assert_eq!(
            count(&node, SyntaxKind::Missing),
            0,
            "{source:?}\n{node:#?}"
        );
        let error = crate::tests::recovery_output::recovery_groups(&node)
            .into_iter()
            .next()
            .expect("one malformed body run");
        assert_eq!(error.text().to_string(), "@", "{source:?}\n{node:#?}");
    }
}

#[test]
fn role_colon_body_keeps_missing_and_shallow_boundaries_pending() {
    let (green, exit, _) = run_role_declaration("role R:", 0, 0, LineEntry::InLine, None);
    assert_eq!(green.to_string(), "role R:");
    assert_eq!(count(&declaration(&green), SyntaxKind::Missing), 1);
    assert!(exit.is_some());

    let source = "role R: ;";
    let (green, exit, remainder) = run_role_declaration(source, 0, 0, LineEntry::InLine, None);
    assert_eq!(green.to_string(), "role R:");
    assert_eq!(remainder, "");
    let node = declaration(&green);
    assert_eq!(count(&node, SyntaxKind::Missing), 1, "{node:#?}");
    let missing = node
        .descendants()
        .find(|child| child.kind() == SyntaxKind::Missing)
        .expect("missing Role body");
    assert_eq!(usize::from(missing.text_range().start()), "role R:".len());
    assert_eq!(
        pending_token_leading(exit, TokenKind::Semicolon, ";", LineEntry::InLine),
        [(SyntaxKind::Whitespace, " ".to_owned())]
    );

    let source = "role R:\nnext";
    let (green, exit, remainder) = run_role_declaration(source, 0, 8_000, LineEntry::InLine, None);
    assert_eq!(green.to_string(), "role R:");
    assert_eq!(remainder, "");
    assert_eq!(count(&declaration(&green), SyntaxKind::Missing), 1);
    assert_eq!(
        pending_tokens(exit, "next", LineEntry::InLine),
        [
            (SyntaxKind::Newline, "\n".to_owned()),
            (SyntaxKind::Identifier, "next".to_owned()),
        ]
    );

    let source = "role R: my x = y; outer";
    let (green, exit, remainder) = run_role_declaration(source, 0, 0, LineEntry::InLine, None);
    assert_eq!(green.to_string(), "role R: my x = y;");
    assert_eq!(remainder, "");
    assert_eq!(token_count(&declaration(&green), SyntaxKind::Semicolon), 1);
    assert_eq!(
        pending_tokens(exit, "outer", LineEntry::InLine),
        [
            (SyntaxKind::Whitespace, " ".to_owned()),
            (SyntaxKind::Identifier, "outer".to_owned()),
        ]
    );

    let source = "role R: else";
    let (green, exit, remainder) = run_role_declaration(
        source,
        crate::lexical::stops::STOP_ELSE,
        0,
        LineEntry::InLine,
        None,
    );
    assert_eq!(green.to_string(), "role R:");
    assert_eq!(remainder, "");
    assert_eq!(count(&declaration(&green), SyntaxKind::Missing), 1);
    assert_eq!(
        pending_tokens(exit, "else", LineEntry::InLine),
        [
            (SyntaxKind::Whitespace, " ".to_owned()),
            (SyntaxKind::Identifier, "else".to_owned()),
        ]
    );
}

#[test]
fn role_delegates_braced_and_indented_statement_recovery() {
    for (source, missing, errors) in [
        ("role R { my x = y", 1, 0),
        ("role R { @\nmy x = y }", 0, 1),
        ("role R:\n  @\n  my x = y", 0, 1),
    ] {
        let (green, _, _) = run_role_declaration(source, 0, 0, LineEntry::InLine, None);
        assert_eq!(green.to_string(), source, "{source:?}");
        let node = declaration(&green);
        assert_eq!(
            count(&node, SyntaxKind::Missing),
            missing,
            "{source:?}\n{node:#?}"
        );
        assert_eq!(
            count(&node, SyntaxKind::Error),
            errors,
            "{source:?}\n{node:#?}"
        );
    }
}

#[test]
fn role_preserves_caller_stop_and_crlf_fence_boundary() {
    let (green, exit, _) = run_role_declaration(
        "role R else",
        crate::lexical::stops::STOP_ELSE,
        1_200,
        LineEntry::InLine,
        None,
    );
    assert_eq!(green.to_string(), "role R");
    assert_eq!(count(&declaration(&green), SyntaxKind::Missing), 1);
    assert_eq!(
        pending_tokens(exit, "else", LineEntry::InLine),
        [
            (SyntaxKind::Whitespace, " ".to_owned()),
            (SyntaxKind::Identifier, "else".to_owned()),
        ]
    );

    let (green, exit, _) = run_role_declaration(
        "role @ else",
        crate::lexical::stops::STOP_ELSE,
        1_200,
        LineEntry::InLine,
        None,
    );
    let node = declaration(&green);
    assert_eq!(green.to_string(), "role @");
    assert_eq!(count(&node, SyntaxKind::Error), 1, "{node:#?}");
    assert_eq!(count(&node, SyntaxKind::Missing), 0, "{node:#?}");
    assert_eq!(
        pending_tokens(exit, "else", LineEntry::InLine),
        [
            (SyntaxKind::Whitespace, " ".to_owned()),
            (SyntaxKind::Identifier, "else".to_owned()),
        ]
    );

    use crate::lexical::item::{BorrowedTarget, Boundary};
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
    let origin = 9_700;
    let accepted = "> > role R {}";
    let source = format!("{accepted}\r\n> > ```\r\nouter");
    let (green, exit, remainder) =
        run_role_declaration(&source, 0, origin, LineEntry::PhysicalStart, Some(&fence));
    assert_eq!(green.to_string(), accepted);
    assert_eq!(remainder, "> > ```\r\nouter");
    let Some(NormalizedExit::Complete(Err(Either::Left(boundary)), LineEntry::PhysicalStart)) =
        exit
    else {
        panic!("Role must preserve the fenced terminal Item")
    };
    let (leading, pending) = emit_terminal_leading_text(boundary);
    assert_eq!(leading, "\r\n");
    assert_eq!(pending.coordinate(), origin + accepted.len() + 2);
    assert!(matches!(
        pending.into_kind(),
        Boundary::BorrowedClose(BorrowedTarget::YumarkFence(_))
    ));
}

#[test]
fn role_private_owner_has_no_source_derives_companion_or_post_brace_attachment() {
    for source in ["role R derives Eq;", "role R with {}"] {
        let (green, _, remainder) = run_role_declaration(source, 0, 0, LineEntry::InLine, None);
        assert_eq!(green.to_string(), source, "{source:?}");
        assert_eq!(remainder, "", "{source:?}");
        let node = declaration(&green);
        assert_eq!(count(&node, SyntaxKind::DerivesClause), 0, "{source:?}");
        assert_eq!(
            count(&node, SyntaxKind::DeclarationCompanion),
            0,
            "{source:?}"
        );
    }

    let (green, _, remainder) =
        run_role_declaration("role R = Source;", 0, 0, LineEntry::InLine, None);
    assert_eq!(green.to_string(), "role R = Source;");
    assert_eq!(remainder, "");
    assert_eq!(count(&declaration(&green), SyntaxKind::Error), 1);

    let (green, exit, remainder) =
        run_role_declaration("role R {} derives Eq", 0, 0, LineEntry::InLine, None);
    assert_eq!(green.to_string(), "role R {}");
    assert_eq!(remainder, " Eq");
    assert_eq!(
        pending_tokens(exit, "derives", LineEntry::InLine),
        [
            (SyntaxKind::Whitespace, " ".to_owned()),
            (SyntaxKind::Identifier, "derives".to_owned()),
        ]
    );
}

#[test]
fn role_braced_completion_hands_off_exactly_one_normalized_successor_item() {
    for (source, expected_leading) in [
        (
            "role R {} next",
            vec![
                (SyntaxKind::Whitespace, " ".to_owned()),
                (SyntaxKind::Identifier, "next".to_owned()),
            ],
        ),
        (
            "role R {}\nnext",
            vec![
                (SyntaxKind::Newline, "\n".to_owned()),
                (SyntaxKind::Identifier, "next".to_owned()),
            ],
        ),
    ] {
        let (green, exit, remainder) = run_role_declaration(source, 0, 0, LineEntry::InLine, None);
        assert_eq!(green.to_string(), "role R {}", "{source:?}");
        assert_eq!(remainder, "", "{source:?}");
        assert_eq!(
            pending_tokens(exit, "next", LineEntry::InLine),
            expected_leading,
            "{source:?}"
        );
    }

    let (green, exit, remainder) = run_role_declaration(
        "role R {} else",
        crate::lexical::stops::STOP_ELSE,
        0,
        LineEntry::InLine,
        None,
    );
    assert_eq!(green.to_string(), "role R {}");
    assert_eq!(remainder, "");
    assert_eq!(
        pending_tokens(exit, "else", LineEntry::InLine),
        [
            (SyntaxKind::Whitespace, " ".to_owned()),
            (SyntaxKind::Identifier, "else".to_owned()),
        ]
    );
}

#[test]
fn role_private_slice_uses_canonical_statement_dispatch() {
    let (green, _) = run_statement("role R;");
    assert_eq!(green.to_string(), "role R;");
    assert_eq!(
        count(&SyntaxNode::new_root(green), SyntaxKind::RoleDeclaration),
        1
    );
}
