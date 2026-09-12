use crate::tests::support::*;

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
    use crate::recovery_record::{
        DeclarationRole, DiagnosticId, ExpectationSources, ExpectedSyntax, GrammarRole,
        RecoveryKind, RecoverySiteKey, RoleDeclarationRole, SyntaxExpectation, TypeRole,
        UnexpectedCategory, UnexpectedSyntax,
    };
    use SyntaxKind::*;
    use std::sync::Arc;

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
        let (green, exit, records, remainder) = typed_role(source, None, 0, None);
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

        // Exact records and reconciliation remain a compatibility oracle only.
        let expected_records = recovery_end
            .map(|end| {
                let missing = end == 5;
                let role = if missing {
                    GrammarRole::Declaration(DeclarationRole::Role(RoleDeclarationRole::Head))
                } else {
                    GrammarRole::Type(TypeRole::Primary)
                };
                let range = 105..100 + end;
                CommittedRecoveryRecord {
                    id: DiagnosticId(0),
                    site: RecoverySiteKey {
                        role,
                        range: range.clone(),
                    },
                    kind: if missing {
                        RecoveryKind::Missing
                    } else {
                        RecoveryKind::Error
                    },
                    unexpected: if missing {
                        Arc::from([])
                    } else if source.contains('~') {
                        // Required Type records each lexical Item; the second
                        // Item's extent includes its Error-owned leading.
                        Arc::from([
                            UnexpectedSyntax::Token {
                                range: 105..106,
                                category: UnexpectedCategory::OtherCharacter,
                            },
                            UnexpectedSyntax::Token {
                                range: 106..109,
                                category: UnexpectedCategory::OperatorLike,
                            },
                        ])
                    } else {
                        Arc::from([UnexpectedSyntax::Token {
                            range: range.clone(),
                            category: UnexpectedCategory::OtherCharacter,
                        }])
                    },
                    expectations: Arc::from([SyntaxExpectation {
                        role,
                        expected: ExpectedSyntax::TypeExpression,
                        range,
                        sources: ExpectationSources::COMMITTED_RECOVERY_RULE,
                    }]),
                    primary_expectation: 0,
                }
            })
            .into_iter()
            .collect::<Vec<_>>();
        assert_eq!(records, expected_records, "{source:?}");
        for seeded in [false, true] {
            let mut seed = records.clone();
            if seeded {
                for record in &mut seed {
                    record.id = DiagnosticId(73);
                }
            }
            let (again, again_exit, frozen, again_remainder) =
                typed_role(source, Some(&seed), 0, None);
            assert_eq!(again, green);
            assert_eq!(frozen, seed);
            assert_eq!(again_remainder, remainder);
            if source == "role @ ;" {
                assert_eq!(
                    pending_token_leading(again_exit, TokenKind::Semicolon, ";", LineEntry::InLine),
                    vec![(Whitespace, " ".to_owned())]
                );
            } else {
                let mut item = pending_item(again_exit, LineEntry::InLine);
                assert!(item.payload_view().is_eof());
                assert_eq!(emit_pending_leading_text(&mut item), "");
            }
        }
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
    let (green, records) = (builder.finish(), recover.finish_recoveries_for_test());
    (green, exit, records, input)
}

#[test]
fn role_body_records_are_exact_and_frozen_with_leading_ownership() {
    use crate::recovery_record::{
        DeclarationRole, Delimiter, DiagnosticId, ExpectationSources, ExpectedSyntax, GrammarRole,
        PunctuationEvidence, RecoveryKind, RecoverySiteKey, RoleDeclarationRole as Role,
        SyntaxExpectation, UnexpectedCategory, UnexpectedSyntax,
    };
    use std::sync::Arc;
    for (source, slot, kind, range, owned, leading) in [
        (
            "role R   ",
            Role::BodyIntroducer,
            RecoveryKind::Missing,
            9..9,
            "role R   ",
            "",
        ),
        (
            "role R  )",
            Role::BodyIntroducer,
            RecoveryKind::Missing,
            6..6,
            "role R",
            "  ",
        ),
        (
            "role R @  ~   ;",
            Role::BodyIntroducer,
            RecoveryKind::Error,
            7..11,
            "role R @  ~   ;",
            "",
        ),
        (
            "role R @ {}",
            Role::BodyIntroducer,
            RecoveryKind::Error,
            7..8,
            "role R @ {}",
            "",
        ),
        (
            "role R @ : x",
            Role::BodyIntroducer,
            RecoveryKind::Error,
            7..8,
            "role R @ : x",
            "",
        ),
        (
            "role R @   ",
            Role::BodyIntroducer,
            RecoveryKind::Error,
            7..8,
            "role R @",
            "   ",
        ),
        (
            "role R @  )",
            Role::BodyIntroducer,
            RecoveryKind::Error,
            7..8,
            "role R @",
            "  ",
        ),
        (
            "role R:   ",
            Role::Body,
            RecoveryKind::Missing,
            7..7,
            "role R:",
            "   ",
        ),
        (
            "role R:  ;",
            Role::Body,
            RecoveryKind::Missing,
            7..7,
            "role R:",
            "  ",
        ),
        (
            "role R:\r\nnext",
            Role::Body,
            RecoveryKind::Missing,
            7..7,
            "role R:",
            "\r\n",
        ),
        (
            "role R:  ]",
            Role::Body,
            RecoveryKind::Missing,
            7..7,
            "role R:",
            "  ",
        ),
        (
            "role R: @  ~   x",
            Role::Body,
            RecoveryKind::Error,
            8..12,
            "role R: @  ~   x",
            "",
        ),
        (
            "role R: @  ;",
            Role::Body,
            RecoveryKind::Error,
            8..9,
            "role R: @",
            "  ",
        ),
        (
            "role R: @   ",
            Role::Body,
            RecoveryKind::Error,
            8..9,
            "role R: @",
            "   ",
        ),
        (
            "role 型: @   ]",
            Role::Body,
            RecoveryKind::Error,
            10..11,
            "role 型: @",
            "   ",
        ),
    ] {
        let (green, exit, records, remainder) = typed_role(source, None, 0, None);
        assert_eq!(green.to_string(), owned, "{source:?}");
        let mut item = pending_item(exit, LineEntry::InLine);
        assert_eq!(emit_pending_leading_text(&mut item), leading, "{source:?}");
        let role = GrammarRole::Declaration(DeclarationRole::Role(slot));
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
        let (again, exit, frozen, again_remainder) = typed_role(source, Some(&seed), 0, None);
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
        .find(|node| node.kind() == SyntaxKind::RoleDeclaration)
        .expect("RoleDeclaration")
}

#[test]
fn role_body_protected_fence_and_contextual_stop_reconcile_exact_handoff() {
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
        ("role R\r\n> > ```\r\nouter", "role R"),
        ("role R:\r\n> > ```\r\nouter", "role R:"),
        ("role R @\r\n> > ```\r\nouter", "role R @"),
        ("role R: @\r\n> > ```\r\nouter", "role R: @"),
    ] {
        let (green, exit, records, remainder) = typed_role(source, None, 0, Some(&fence));
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
        let (again, exit, frozen, remainder) = typed_role(source, Some(&records), 0, Some(&fence));
        assert_eq!(again, green);
        assert_eq!(frozen, records);
        assert_eq!(remainder, "> > ```\r\nouter");
        let (leading, boundary) =
            emit_terminal_leading_text(pending_item(exit, LineEntry::PhysicalStart));
        assert_eq!(leading, "\r\n");
        assert_eq!(boundary.coordinate(), 100 + owned.len() + 2);
    }
    for owned in ["role R", "role R:", "role R @", "role R: @"] {
        let source = format!("{owned}  else suffix");
        let (green, exit, records, remainder) = typed_role(&source, None, STOP_ELSE, None);
        assert_eq!(green.to_string(), owned);
        assert_eq!(records.len(), 1);
        assert_eq!(remainder, " suffix");
        let mut item = pending_item(exit, LineEntry::InLine);
        assert_eq!(emit_pending_leading_text(&mut item), "  ");
        assert_eq!(item.payload_view().spelling(), Some("else"));
        let (again, exit, frozen, remainder) = typed_role(&source, Some(&records), STOP_ELSE, None);
        assert_eq!(again, green);
        assert_eq!(frozen, records);
        assert_eq!(remainder, " suffix");
        let mut item = pending_item(exit, LineEntry::InLine);
        assert_eq!(emit_pending_leading_text(&mut item), "  ");
        assert_eq!(item.payload_view().spelling(), Some("else"));
    }
}

#[test]
fn role_body_recovery_retains_head_and_statement_child_owners() {
    use crate::recovery_record::{BindingRole, DeclarationRole, GrammarRole, RoleDeclarationRole};
    for (source, role) in [
        (
            "role @ ;",
            GrammarRole::Type(crate::recovery_record::TypeRole::Primary),
        ),
        (
            "role )",
            GrammarRole::Declaration(DeclarationRole::Role(RoleDeclarationRole::Head)),
        ),
    ] {
        let (_, _, records, _) = typed_role(source, None, 0, None);
        assert_eq!(records.len(), 1, "{source}");
        assert_eq!(records[0].site.role, role);
    }
    for source in ["role R: my x =", "role R {my x =}", "role R:\n  my x ="] {
        let (green, _, records, _) = typed_role(source, None, 0, None);
        assert_eq!(records.len(), 1, "{source}");
        assert_eq!(
            records[0].site.role,
            GrammarRole::Declaration(DeclarationRole::Binding(BindingRole::Body))
        );
        let (again, _, frozen, _) = typed_role(source, Some(&records), 0, None);
        assert_eq!(again, green);
        assert_eq!(frozen, records);
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
