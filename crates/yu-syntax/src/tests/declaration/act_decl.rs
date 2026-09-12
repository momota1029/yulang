use crate::tests::support::*;

fn assert_act_body_schema(source: &str, expected: &[(SyntaxKind, usize)]) -> SyntaxNode {
    let (green, _, remainder) = run_act_declaration(source, 0, 0, LineEntry::InLine, None);
    assert_eq!(green.to_string(), source);
    assert_eq!(remainder, "");
    let node = declaration(&green);
    assert!(
        !node
            .descendants()
            .any(|child| child.kind() == SyntaxKind::Invalid)
    );
    let mut offset = 0;
    let expected = expected
        .iter()
        .map(|&(kind, len)| {
            let range = offset..offset + len;
            offset += len;
            (kind, range)
        })
        .collect::<Vec<_>>();
    assert_eq!(
        node.children_with_tokens()
            .map(|element| {
                assert_eq!(element.parent().as_ref(), Some(&node));
                if element.kind() == SyntaxKind::Error {
                    assert!(element.as_token().is_some());
                }
                if element.kind() == SyntaxKind::Missing {
                    assert!(
                        element
                            .as_node()
                            .unwrap()
                            .children_with_tokens()
                            .next()
                            .is_none()
                    );
                }
                (
                    element.kind(),
                    usize::from(element.text_range().start())
                        ..usize::from(element.text_range().end()),
                )
            })
            .collect::<Vec<_>>(),
        expected,
        "{source:?}"
    );
    node
}

#[test]
fn act_body_introducer_schema_uses_completed_type_and_native_retry_boundaries() {
    use SyntaxKind::*;
    for (prefix, mut head) in [
        (
            "act A",
            vec![(ActKw, 3), (Whitespace, 1), (TypeExpression, 1)],
        ),
        (
            "act A = B",
            vec![
                (ActKw, 3),
                (Whitespace, 1),
                (TypeExpression, 1),
                (Whitespace, 1),
                (Equals, 1),
                (Whitespace, 1),
                (TypeExpression, 1),
            ],
        ),
    ] {
        // Completed head/source terminal absence has no recovery child.
        assert_act_body_schema(prefix, &head);
        head.extend([(Whitespace, 1), (Error, 1), (Error, 1), (Error, 1)]);
        assert_act_body_schema(&format!("{prefix} @ %"), &head);
        for (retry, tail) in [
            (";", vec![(Semicolon, 1)]),
            ("{}", vec![(BracedStatementBlockExpression, 2)]),
            (": my x = y", vec![(Colon, 1), (Statement, 9)]),
        ] {
            let mut expected = head.clone();
            expected.push((Whitespace, 1));
            expected.extend(tail);
            assert_act_body_schema(&format!("{prefix} @ % {retry}"), &expected);
        }
    }
    // The same direct Error before the head TypeExpression belongs to Head.
    assert_act_body_schema(
        "act @ A;",
        &[
            (ActKw, 3),
            (Whitespace, 1),
            (Error, 1),
            (TypeExpression, 2),
            (Semicolon, 1),
        ],
    );
}

#[test]
fn act_source_schema_uses_equals_and_ordered_required_type_evidence() {
    use crate::recovery_record::{
        ActDeclarationRole, DeclarationRole, GrammarRole, RecoveryKind, TypeRole,
    };
    use SyntaxKind::*;

    for (source, suffix, missing_at) in [
        (
            "act A = ;",
            vec![
                (TypeExpression, true, 7..7, ""),
                (Whitespace, false, 7..8, " "),
                (Semicolon, false, 8..9, ";"),
            ],
            Some(7),
        ),
        (
            "act = B;",
            vec![
                (Whitespace, false, 5..6, " "),
                (TypeExpression, true, 6..7, "B"),
                (Semicolon, false, 7..8, ";"),
            ],
            Some(3),
        ),
        (
            "act A = @;",
            vec![
                (Whitespace, false, 7..8, " "),
                (Error, false, 8..9, "@"),
                (Semicolon, false, 9..10, ";"),
            ],
            None,
        ),
        (
            "act A = @ B;",
            vec![
                (Whitespace, false, 7..8, " "),
                (Error, false, 8..9, "@"),
                (TypeExpression, true, 9..11, " B"),
                (Semicolon, false, 11..12, ";"),
            ],
            None,
        ),
        (
            "act A = B;",
            vec![
                (Whitespace, false, 7..8, " "),
                (TypeExpression, true, 8..9, "B"),
                (Semicolon, false, 9..10, ";"),
            ],
            None,
        ),
        (
            "act A = @ % B;",
            vec![
                (Whitespace, false, 7..8, " "),
                (Error, false, 8..9, "@"),
                (Error, false, 9..10, " "),
                (Error, false, 10..11, "%"),
                (TypeExpression, true, 11..13, " B"),
                (Semicolon, false, 13..14, ";"),
            ],
            None,
        ),
    ] {
        let (green, exit, records, remainder) = typed_act(source, None, 0, None);
        assert_eq!(green.to_string(), source, "{source:?}");
        assert_eq!(remainder, "");
        let (canonical, _, canonical_remainder) =
            run_statement_normalized(source, 100, LineEntry::InLine, None);
        assert_eq!(canonical_remainder, "");
        let act = declaration(&canonical);
        assert_eq!(act.green(), declaration(&green).green());
        let statement = act.parent().expect("canonical Statement");
        assert_eq!(statement.kind(), Statement);
        let root = statement.parent().expect("Root");
        assert_eq!(root.kind(), Root);
        assert!(root.parent().is_none());
        assert_eq!(root.to_string(), source);
        assert_eq!(statement.to_string(), source);
        assert_eq!(act.to_string(), source);
        assert!(
            !root
                .descendants_with_tokens()
                .any(|child| child.kind() == Invalid)
        );

        let mut expected = if missing_at == Some(3) {
            vec![
                (ActKw, false, 0..3, "act"),
                (TypeExpression, true, 3..3, ""),
                (Whitespace, false, 3..4, " "),
                (Equals, false, 4..5, "="),
            ]
        } else {
            vec![
                (ActKw, false, 0..3, "act"),
                (Whitespace, false, 3..4, " "),
                (TypeExpression, true, 4..5, "A"),
                (Whitespace, false, 5..6, " "),
                (Equals, false, 6..7, "="),
            ]
        };
        expected.extend(suffix);
        let children = act.children_with_tokens().collect::<Vec<_>>();
        assert_eq!(children.len(), expected.len());
        for (child, (kind, node, range, text)) in children.iter().zip(expected) {
            assert_eq!(child.parent(), Some(act.clone()));
            assert_eq!(child.kind(), kind);
            assert_eq!(child.as_node().is_some(), node);
            assert_eq!(
                child.text_range(),
                rowan::TextRange::new(range.start.into(), range.end.into())
            );
            assert_eq!(child.to_string(), text);
        }

        // The actual Equals separates Head from Source. The collision control
        // retains an empty Head before Equals, never a missing Source.
        let equals = children
            .iter()
            .position(|child| child.kind() == Equals)
            .unwrap();
        let head = children[..equals]
            .iter()
            .find_map(|child| child.as_node())
            .unwrap();
        assert_eq!(head.kind(), TypeExpression);
        assert_eq!(head.text_range().is_empty(), missing_at == Some(3));
        let source_slot = &children[equals + 1..];
        let source_type = source_slot.iter().find_map(|child| child.as_node());
        if let Some(source_type) = source_type {
            assert_eq!(source_type.kind(), TypeExpression);
            assert_eq!(source_type.text_range().is_empty(), missing_at == Some(7));
        } else {
            assert_eq!(source, "act A = @;");
        }
        let errors = source_slot
            .iter()
            .skip_while(|child| child.kind() == Whitespace)
            .take_while(|child| child.kind() == Error)
            .collect::<Vec<_>>();
        assert_eq!(
            errors.len(),
            if source.contains('%') {
                3
            } else {
                usize::from(source.contains('@'))
            }
        );
        assert_eq!(
            root.descendants_with_tokens()
                .filter(|child| child.kind() == Error)
                .count(),
            errors.len()
        );
        for pair in errors.windows(2) {
            assert_eq!(pair[0].text_range().end(), pair[1].text_range().start());
        }
        if let Some(first) = errors.first() {
            assert_eq!(first.text_range().start(), 8.into());
            let end = if source.contains('%') { 11 } else { 9 };
            assert_eq!(errors.last().unwrap().text_range().end(), end.into());
            if let Some(source_type) = source_type {
                assert_eq!(source_type.text_range().start(), end.into());
                let leading = source_type.first_child_or_token().unwrap();
                assert!(leading.as_token().is_some());
                assert_eq!(leading.parent(), Some(source_type.clone()));
                assert_eq!(leading.kind(), Whitespace);
                assert_eq!(
                    leading.text_range(),
                    rowan::TextRange::new(end.into(), (end + 1).into())
                );
                assert_eq!(leading.to_string(), " ");
            }
        }
        let missing = root
            .descendants()
            .filter(|child| child.kind() == Missing)
            .collect::<Vec<_>>();
        assert_eq!(missing.len(), usize::from(missing_at.is_some()));
        if let Some(at) = missing_at {
            let parent = missing[0].parent().unwrap();
            assert_eq!(
                parent,
                if at == 3 {
                    head.clone()
                } else {
                    source_type.unwrap().clone()
                }
            );
            assert_eq!(parent.children_with_tokens().count(), 1);
            assert_eq!(parent.text_range(), rowan::TextRange::empty(at.into()));
            assert_eq!(missing[0].text_range(), parent.text_range());
            assert_eq!(missing[0].to_string(), "");
            assert_eq!(missing[0].children_with_tokens().count(), 0);
        }

        let assert_handoff = |exit| {
            let mut item = match exit {
                Some(NormalizedExit::Complete(Err(Either::Left(item)), entry)) => {
                    assert_eq!(entry, LineEntry::InLine);
                    item
                }
                Some(NormalizedExit::Complete(Err(Either::Right(end)), entry)) => {
                    assert_eq!(entry, LineEntry::InLine);
                    end.item
                }
                _ => panic!("expected pending EOF"),
            };
            // Required Type preserves the body starter for Act; Act then owns
            // that semicolon even after an absent or malformed Source.
            assert!(item.payload_view().is_eof());
            assert_eq!(emit_pending_leading_text(&mut item), "");
        };
        assert_handoff(exit);
        // Compatibility only: the CST checks above identify the owning slot.
        assert_eq!(
            records.len(),
            usize::from(missing_at.is_some() || !errors.is_empty())
        );
        if let Some(record) = records.first() {
            if let Some(at) = missing_at {
                assert_eq!(record.kind, RecoveryKind::Missing);
                assert_eq!(
                    record.site.role,
                    GrammarRole::Declaration(DeclarationRole::Act(if at == 3 {
                        ActDeclarationRole::Head
                    } else {
                        ActDeclarationRole::Source
                    }))
                );
                assert_eq!(record.site.range, 100 + at as usize..100 + at as usize);
            } else {
                assert_eq!(record.kind, RecoveryKind::Error);
                assert_eq!(record.site.role, GrammarRole::Type(TypeRole::Primary));
                assert_eq!(
                    record.site.range,
                    108..if source.contains('%') { 111 } else { 109 }
                );
            }
        }
        let (again, again_exit, frozen, again_remainder) =
            typed_act(source, Some(&records), 0, None);
        assert_eq!(again, green);
        assert_eq!(frozen, records);
        assert_eq!(again_remainder, remainder);
        assert_handoff(again_exit);
    }
}

#[test]
fn act_inline_body_schema_requires_direct_colon_and_preserves_child_ownership() {
    use SyntaxKind::*;
    let prefix = [(ActKw, 3), (Whitespace, 1), (TypeExpression, 1), (Colon, 1)];
    for (suffix, tail) in [
        ("", vec![(Missing, 0)]),
        (
            " @ %",
            vec![(Whitespace, 1), (Error, 1), (Error, 1), (Error, 1)],
        ),
        (
            " @ % my x = y",
            vec![
                (Whitespace, 1),
                (Error, 1),
                (Error, 1),
                (Error, 1),
                (Statement, 9),
            ],
        ),
    ] {
        let mut expected = prefix.to_vec();
        expected.extend(tail);
        let node = assert_act_body_schema(&format!("act A:{suffix}"), &expected);
        if let Some(statement) = node.children().find(|child| child.kind() == Statement) {
            let leading = statement.first_token().unwrap();
            assert_eq!(leading.kind(), Whitespace);
            assert_eq!(
                leading.text_range(),
                rowan::TextRange::new(10.into(), 11.into())
            );
        }
    }
    let mut expected = prefix.to_vec();
    expected.push((Statement, 7));
    let node = assert_act_body_schema("act A: my x =", &expected);
    let missing = node
        .descendants()
        .find(|child| child.kind() == Missing)
        .unwrap();
    assert_eq!(missing.text_range(), rowan::TextRange::empty(13.into()));
    assert_eq!(missing.parent().unwrap().kind(), BindingBody);
    assert!(
        missing
            .ancestors()
            .any(|ancestor| ancestor.kind() == Statement)
    );
}

fn act_record(
    slot: crate::recovery_record::ActDeclarationRole,
    kind: crate::recovery_record::RecoveryKind,
    range: std::ops::Range<usize>,
) -> CommittedRecoveryRecord {
    use crate::recovery_record::*;
    use std::sync::Arc;
    let role = GrammarRole::Declaration(DeclarationRole::Act(slot));
    let expected = if slot == ActDeclarationRole::BodyIntroducer {
        vec![
            ExpectedSyntax::Punctuation(PunctuationEvidence::Semicolon),
            ExpectedSyntax::Punctuation(PunctuationEvidence::Open(Delimiter::Brace)),
            ExpectedSyntax::Punctuation(PunctuationEvidence::Colon),
        ]
    } else {
        vec![ExpectedSyntax::Statement]
    };
    CommittedRecoveryRecord {
        id: DiagnosticId(0),
        site: RecoverySiteKey {
            role,
            range: range.clone(),
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
                sources: ExpectationSources::COMMITTED_RECOVERY_RULE,
            })
            .collect::<Vec<_>>()
            .into(),
        primary_expectation: 0,
    }
}

#[test]
fn act_typed_runs_retry_each_starter_and_statement_with_exact_records() {
    use crate::recovery_record::{ActDeclarationRole as R, RecoveryKind as K};
    for (source, slot, range) in [
        ("act A @ % ;", R::BodyIntroducer, 106..109),
        ("act A @ {} derives Eq", R::BodyIntroducer, 106..107),
        ("act A @ : my x = y", R::BodyIntroducer, 106..107),
        ("act A: @ % my x = y", R::Body, 107..110),
        ("act 名: @ my x = y", R::Body, 109..110),
    ] {
        let (green, _, records, rest) = typed_act(source, None, 0, None);
        assert_eq!(green.to_string(), source, "{source}");
        assert_eq!(rest, "");
        assert_eq!(records, [act_record(slot, K::Error, range)], "{source}");
        let (again, _, frozen, rest) = typed_act(source, Some(&records), 0, None);
        assert_eq!(again, green);
        assert_eq!(frozen, records);
        assert_eq!(rest, "");
    }
}

#[test]
fn act_typed_absence_and_post_error_boundaries_preserve_whole_items() {
    use crate::recovery_record::{ActDeclarationRole as R, RecoveryKind as K};
    for (owned, slot, kind, range) in [
        ("act A:", R::Body, K::Missing, 106..106),
        ("act A: @", R::Body, K::Error, 107..108),
        ("act A @", R::BodyIntroducer, K::Error, 106..107),
    ] {
        for suffix in ["  ", "  ) tail", "  , tail", "  else tail", "\r\nnext tail"] {
            let source = format!("{owned}{suffix}");
            let (green, _, records, _) = typed_act(&source, None, STOP_ELSE, None);
            assert_eq!(green.to_string(), owned, "{source:?}");
            assert_eq!(
                records,
                [act_record(slot, kind, range.clone())],
                "{source:?}"
            );
            for frozen in [None, Some(records.as_slice())] {
                let (again, exit, actual, rest) = typed_act(&source, frozen, STOP_ELSE, None);
                assert_eq!(again, green);
                assert_eq!(actual, records);
                let mut item = match exit {
                    Some(NormalizedExit::Complete(Err(Either::Left(item)), _)) => item,
                    Some(NormalizedExit::Complete(Err(Either::Right(end)), _)) => end.item,
                    _ => panic!("pending {source:?}"),
                };
                let leading = emit_pending_leading_text(&mut item);
                let payload = item.payload_view().spelling().unwrap_or("");
                assert_eq!(format!("{owned}{leading}{payload}{rest}"), source);
            }
        }
    }
    let (green, _, records, _) = typed_act("act A: ;", None, 0, None);
    assert_eq!(green.to_string(), "act A:");
    assert_eq!(records, [act_record(R::Body, K::Missing, 106..106)]);
}

#[test]
fn act_typed_bodyless_and_attachment_controls_remain_zero_recovery() {
    for source in [
        "act A",
        "act A = B",
        "act A derives Eq with {}",
        "act A = B derives Eq with {}",
        "act A {} derives Eq",
        "act A: my x = y",
    ] {
        let (green, _, records, rest) = typed_act(source, None, 0, None);
        assert_eq!(green.to_string(), source);
        assert!(records.is_empty(), "{source}");
        assert_eq!(rest, "");
        let (again, _, frozen, _) = typed_act(source, Some(&records), 0, None);
        assert_eq!(again, green);
        assert_eq!(frozen, records);
    }
}

#[test]
fn act_typed_bodyless_closing_owner_boundary_keeps_the_whole_item() {
    let source = "act A  } tail";
    let expected = [];
    for frozen in [None, Some(expected.as_slice())] {
        let (green, exit, records, rest) = typed_act(source, frozen, 0, None);
        assert_eq!(green.to_string(), "act A");
        assert_eq!(records, expected);
        assert_eq!(rest, " tail");
        let Some(NormalizedExit::Complete(Err(Either::Left(mut item)), LineEntry::InLine)) = exit
        else {
            panic!("the closing owner's brace must remain pending")
        };
        assert_eq!(token_kind(&item), Some(TokenKind::RBrace));
        let successor = 100 + source.len() - rest.len();
        assert_eq!(successor, 108);
        assert_eq!(item.extent(successor).recovery_range(), 105..108);
        assert_eq!(emit_pending_leading_text(&mut item), "  ");
        assert_eq!(item.payload_view().spelling(), Some("}"));
    }
}

#[test]
fn act_typed_fence_absence_and_error_keep_crlf_and_abstract_coordinate() {
    use crate::lexical::yumark::{FenceOpener, FencePrefixPolicy};
    use crate::recovery_record::{ActDeclarationRole as R, RecoveryKind as K};
    let fence = FenceBoundary {
        opener: FenceOpener {
            line: 0,
            marker: 0..3,
            marker_width: 3,
        },
        prefix_policy: FencePrefixPolicy::ActivePrefixQuote { depth: 2, base: 0 },
        close_column: 0,
    };
    for (owned, expected) in [
        ("act A", None),
        ("act A:", Some(act_record(R::Body, K::Missing, 108..108))),
        (
            "act A @",
            Some(act_record(R::BodyIntroducer, K::Error, 106..107)),
        ),
        ("act A: @", Some(act_record(R::Body, K::Error, 107..108))),
    ] {
        let source = format!("{owned}\r\n> > ```\r\nouter");
        let expected: Vec<_> = expected.into_iter().collect();
        for frozen in [None, Some(expected.as_slice())] {
            let (green, exit, records, rest) = typed_act(&source, frozen, 0, Some(&fence));
            assert_eq!(green.to_string(), owned);
            assert_eq!(records, expected);
            assert_eq!(rest, "> > ```\r\nouter");
            let Some(NormalizedExit::Complete(Err(Either::Left(item)), LineEntry::PhysicalStart)) =
                exit
            else {
                panic!("fence pending")
            };
            let (leading, boundary) = emit_terminal_leading_text(item);
            assert_eq!(leading, "\r\n");
            assert_eq!(boundary.coordinate(), 100 + owned.len() + 2);
        }
    }
}

#[test]
fn act_typed_shell_preserves_head_source_and_child_owners_without_cascade() {
    use crate::recovery_record::{
        ActDeclarationRole as R, BindingRole, DeclarationRole, GrammarRole,
    };
    for (source, role) in [
        (
            "act;",
            GrammarRole::Declaration(DeclarationRole::Act(R::Head)),
        ),
        (
            "act A = ;",
            GrammarRole::Declaration(DeclarationRole::Act(R::Source)),
        ),
        (
            "act A: my x =",
            GrammarRole::Declaration(DeclarationRole::Binding(BindingRole::Body)),
        ),
    ] {
        let (green, _, records, _) = typed_act(source, None, 0, None);
        assert_eq!(records.len(), 1, "{source}");
        assert_eq!(records[0].site.role, role);
        let (again, _, frozen, _) = typed_act(source, Some(&records), 0, None);
        assert_eq!(again, green);
        assert_eq!(frozen, records);
    }
}

fn typed_act<'s>(
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
    let exit = act_declaration_witness(
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

fn declaration(green: &GreenNode) -> SyntaxNode {
    SyntaxNode::new_root(green.clone())
        .descendants()
        .find(|node| node.kind() == SyntaxKind::ActDeclaration)
        .expect("ActDeclaration")
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

fn pending_word(exit: Option<NormalizedExit>, word: &str, leading: &str) {
    let mut item = match exit {
        Some(NormalizedExit::Complete(Err(Either::Left(item)), _)) => item,
        Some(NormalizedExit::Complete(Err(Either::Right(end)), _)) => end.item,
        _ => panic!("{word:?} must remain pending"),
    };
    assert_eq!(item.payload_view().spelling(), Some(word));
    assert_eq!(emit_pending_leading_text(&mut item), leading);
}

fn pending_word_tokens(
    exit: Option<NormalizedExit>,
    word: &str,
    line_entry: LineEntry,
) -> Vec<(SyntaxKind, String)> {
    let mut item = match exit {
        Some(NormalizedExit::Complete(Err(Either::Left(item)), actual_entry)) => {
            assert_eq!(actual_entry, line_entry);
            item
        }
        Some(NormalizedExit::Complete(Err(Either::Right(end)), actual_entry)) => {
            assert_eq!(actual_entry, line_entry);
            end.item
        }
        _ => panic!("{word:?} must remain pending"),
    };
    assert_eq!(item.payload_view().spelling(), Some(word));

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

#[test]
fn act_private_shell_builds_head_source_and_each_body_form() {
    for (source, body_kind) in [
        ("act Console::Read;", None),
        ("act local 't = var 't", None),
        (
            "our act A { my x = y }",
            Some(SyntaxKind::BracedStatementBlockExpression),
        ),
        ("pub act A: my x = y;", None),
        (
            "act A:\n  my x = y",
            Some(SyntaxKind::IndentedStatementBlock),
        ),
    ] {
        let (green, exit, remainder) = run_act_declaration(source, 0, 0, LineEntry::InLine, None);
        assert!(exit.is_some(), "{source:?}");
        assert_eq!(green.to_string(), source, "{source:?}");
        assert_eq!(remainder, "", "{source:?}");
        let node = declaration(&green);
        assert_eq!(count(&node, SyntaxKind::Error), 0, "{source:?}\n{node:#?}");
        assert_eq!(
            count(&node, SyntaxKind::Missing),
            0,
            "{source:?}\n{node:#?}"
        );
        assert_eq!(token_count(&node, SyntaxKind::ActKw), 1, "{source:?}");
        if let Some(kind) = body_kind {
            assert_eq!(count(&node, kind), 1, "{source:?}\n{node:#?}");
        }
    }
}

#[test]
fn act_my_intro_requires_the_raw_head_candidate_without_consuming_a_rejection() {
    for source in ["my act = value", "my act;", "my act"] {
        let (green, exit, remainder) = run_act_declaration(source, 0, 700, LineEntry::InLine, None);
        assert!(exit.is_none(), "{source:?}");
        assert_eq!(green.to_string(), "", "{source:?}");
        assert_eq!(remainder, source, "{source:?}");
    }

    for source in [
        "my act next = last",
        "my act't = last",
        "my act _hidden;",
        "my act $hidden = value",
        "my act &hidden = value",
    ] {
        let (green, exit, _) = run_act_declaration(source, 0, 0, LineEntry::InLine, None);
        assert!(exit.is_some(), "{source:?}");
        assert_eq!(green.to_string(), source, "{source:?}");
        assert_eq!(token_count(&declaration(&green), SyntaxKind::ActKw), 1);
    }
}

#[test]
fn act_post_head_and_post_source_companions_terminate_the_declaration() {
    for (source, accepted, equals) in [
        ("act A with {} = B with {}", "act A with {}", 0),
        ("act A = B with {}: tail", "act A = B with {}", 1),
    ] {
        let (green, exit, _) = run_act_declaration(source, 0, 0, LineEntry::InLine, None);
        assert_eq!(green.to_string(), accepted, "{source:?}");
        let node = declaration(&green);
        assert_eq!(count(&node, SyntaxKind::DeclarationCompanion), 1);
        assert_eq!(token_count(&node, SyntaxKind::WithKw), 1);
        assert_eq!(token_count(&node, SyntaxKind::Equals), equals);
        assert_eq!(
            count(&node, SyntaxKind::Missing),
            0,
            "{source:?}\n{node:#?}"
        );
        assert!(exit.is_some());
    }
}

#[test]
fn act_header_derives_precedes_the_terminating_companion_at_both_positions() {
    for (source, equals) in [
        ("act A derives Eq with {}", 0),
        ("act A derives Eq = B derives Copy with {}", 1),
    ] {
        let (green, _, remainder) = run_act_declaration(source, 0, 0, LineEntry::InLine, None);
        assert_eq!(green.to_string(), source, "{source:?}");
        assert_eq!(remainder, "", "{source:?}");
        let node = declaration(&green);
        assert_eq!(count(&node, SyntaxKind::DerivesClause), equals + 1);
        assert_eq!(count(&node, SyntaxKind::DeclarationCompanion), 1);
        assert_eq!(token_count(&node, SyntaxKind::Equals), equals);
    }
}

#[test]
fn act_fresh_derives_stays_a_type_but_nested_with_does_not_escape_its_episode() {
    for source in [
        "act derives Eq;",
        "act A = derives Eq;",
        "act (A with B) with {}",
        "act A = (B with C) with {}",
    ] {
        let (green, _, remainder) = run_act_declaration(source, 0, 0, LineEntry::InLine, None);
        assert_eq!(green.to_string(), source, "{source:?}");
        assert_eq!(remainder, "", "{source:?}");
        let node = declaration(&green);
        if source.contains("(A") || source.contains("(B") {
            assert_eq!(count(&node, SyntaxKind::DeclarationCompanion), 1);
            assert_eq!(token_count(&node, SyntaxKind::WithKw), 1);
        } else {
            assert_eq!(count(&node, SyntaxKind::DerivesClause), 0);
            assert_eq!(count(&node, SyntaxKind::DeclarationCompanion), 0);
        }
    }
}

#[test]
fn act_missing_head_or_source_hands_the_same_with_to_one_companion() {
    for (source, equals) in [("act with {}", 0), ("act A = with {}", 1)] {
        let (green, _, remainder) = run_act_declaration(source, 0, 0, LineEntry::InLine, None);
        assert_eq!(green.to_string(), source, "{source:?}");
        assert_eq!(remainder, "", "{source:?}");
        let node = declaration(&green);
        assert_eq!(
            count(&node, SyntaxKind::Missing),
            1,
            "{source:?}\n{node:#?}"
        );
        assert_eq!(count(&node, SyntaxKind::DeclarationCompanion), 1);
        assert_eq!(token_count(&node, SyntaxKind::Equals), equals);
    }
}

#[test]
fn act_recovery_preserves_body_starters_and_avoids_same_cause_cascades() {
    for (source, missing, errors) in [
        ("act;", 1, 0),
        ("act = B;", 1, 0),
        ("act A = ;", 1, 0),
        ("act A:", 1, 0),
        ("act @ A;", 0, 1),
        ("act A: @ my x = y", 0, 1),
    ] {
        let (green, _, _) = run_act_declaration(source, 0, 0, LineEntry::InLine, None);
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
fn act_shallow_colon_body_returns_the_exact_next_item() {
    let origin = 8_700;
    let accepted = "act A:";
    let source = format!("{accepted}\nnext");
    let (green, exit, remainder) = run_act_declaration(&source, 0, origin, LineEntry::InLine, None);
    assert_eq!(green.to_string(), accepted);
    assert_eq!(remainder, "");
    let node = declaration(&green);
    assert_eq!(count(&node, SyntaxKind::Missing), 1, "{node:#?}");
    assert_eq!(count(&node, SyntaxKind::Error), 0, "{node:#?}");
    let pending = pending_word_tokens(exit, "next", LineEntry::InLine);
    assert_eq!(
        pending,
        [
            (SyntaxKind::Newline, "\n".to_owned()),
            (SyntaxKind::Identifier, "next".to_owned()),
        ],
    );
    assert_eq!(
        green.to_string()
            + &pending
                .iter()
                .map(|(_, text)| text.as_str())
                .collect::<String>(),
        source,
    );
    let pending_payload_coordinate = origin + source.len()
        - remainder.len()
        - pending
            .last()
            .expect("the pending payload token must be emitted")
            .1
            .len();
    assert_eq!(pending_payload_coordinate, origin + accepted.len() + 1);
}

#[test]
fn act_companion_accepts_only_strictly_deeper_newline_gaps_at_both_positions() {
    for source in ["act A\n  with {}", "act A = B\n  with {}"] {
        let (green, exit, remainder) = run_act_declaration(source, 0, 0, LineEntry::InLine, None);
        assert_eq!(green.to_string(), source, "{source:?}");
        assert_eq!(remainder, "", "{source:?}");
        let node = declaration(&green);
        assert_eq!(count(&node, SyntaxKind::DeclarationCompanion), 1);
        assert_eq!(token_count(&node, SyntaxKind::WithKw), 1);
        assert_eq!(
            count(&node, SyntaxKind::Missing),
            0,
            "{source:?}\n{node:#?}"
        );
        assert_eq!(count(&node, SyntaxKind::Error), 0, "{source:?}\n{node:#?}");
        assert!(exit.is_some(), "{source:?}");
    }
}

#[test]
fn act_companion_word_probe_is_exact_at_both_positions() {
    for source in ["act A withx", "act A = B within"] {
        let (green, exit, remainder) = run_act_declaration(source, 0, 0, LineEntry::InLine, None);
        assert_eq!(green.to_string(), source, "{source:?}");
        assert_eq!(remainder, "", "{source:?}");
        let node = declaration(&green);
        assert_eq!(count(&node, SyntaxKind::DeclarationCompanion), 0);
        assert_eq!(token_count(&node, SyntaxKind::WithKw), 0);
        assert!(exit.is_some(), "{source:?}");
    }
}

#[test]
fn act_malformed_head_or_source_recovers_once_before_the_exact_companion() {
    for source in ["act @ with {}", "act A = @ with {}"] {
        let (green, exit, remainder) = run_act_declaration(source, 0, 0, LineEntry::InLine, None);
        assert_eq!(green.to_string(), source, "{source:?}");
        assert_eq!(remainder, "", "{source:?}");
        let node = declaration(&green);
        assert_eq!(count(&node, SyntaxKind::Error), 1, "{source:?}\n{node:#?}");
        assert_eq!(
            count(&node, SyntaxKind::Missing),
            0,
            "{source:?}\n{node:#?}"
        );
        assert_eq!(count(&node, SyntaxKind::DeclarationCompanion), 1);
        assert_eq!(token_count(&node, SyntaxKind::WithKw), 1);
        assert!(exit.is_some(), "{source:?}");
    }
}

#[test]
fn act_rejects_post_body_companion_but_keeps_actual_brace_trailing_derives() {
    for (source, accepted, derives, pending, leading) in [
        ("act A{} derives Eq", "act A{} derives Eq", 1, None, ""),
        ("act A{} with {}", "act A{}", 0, Some("with"), " "),
        ("act A; with {}", "act A;", 0, Some("with"), " "),
        ("act A:\n  x\nwith {}", "act A:\n  x", 0, Some("with"), "\n"),
    ] {
        let (green, exit, _) = run_act_declaration(source, 0, 0, LineEntry::InLine, None);
        assert_eq!(green.to_string(), accepted, "{source:?}");
        let node = declaration(&green);
        assert_eq!(
            count(&node, SyntaxKind::DerivesClause),
            derives,
            "{source:?}"
        );
        assert_eq!(
            count(&node, SyntaxKind::DeclarationCompanion),
            0,
            "{source:?}"
        );
        if let Some(word) = pending {
            pending_word(exit, word, leading);
        }
    }
}

#[test]
fn act_caller_stop_and_rejected_gap_leave_with_unchanged() {
    let (green, exit, _) = run_act_declaration(
        "act A with {}",
        crate::lexical::stops::STOP_WITH,
        0,
        LineEntry::InLine,
        None,
    );
    assert_eq!(green.to_string(), "act A");
    assert_eq!(
        count(&declaration(&green), SyntaxKind::DeclarationCompanion),
        0
    );
    pending_word(exit, "with", " ");

    let (green, exit, _) = run_act_declaration("act A\nwith {}", 0, 0, LineEntry::InLine, None);
    assert_eq!(green.to_string(), "act A");
    pending_word(exit, "with", "\n");
}

#[test]
fn act_companion_preserves_exact_remainder_origin_line_entry_and_fence_boundary() {
    let origin = 9_700;
    let accepted = "act A with {}";
    let source = format!("{accepted}  outer tail");
    let (green, exit, remainder) = run_act_declaration(&source, 0, origin, LineEntry::InLine, None);
    assert_eq!(green.to_string(), accepted);
    assert_eq!(remainder, "  outer tail");
    let Some(NormalizedExit::Complete(Ok(()), LineEntry::InLine)) = exit else {
        panic!("Act companion must complete before scanning its outer remainder")
    };

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
    let accepted = "> > act A = B with: my x = y";
    let source = format!("{accepted}\r\n> > ```\r\nouter");
    let (green, exit, remainder) =
        run_act_declaration(&source, 0, origin, LineEntry::PhysicalStart, Some(&fence));
    assert_eq!(green.to_string(), accepted);
    assert_eq!(remainder, "> > ```\r\nouter");
    let Some(NormalizedExit::Complete(Err(Either::Left(boundary)), LineEntry::PhysicalStart)) =
        exit
    else {
        panic!("Act companion must preserve the fenced terminal Item")
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
fn act_private_slice_uses_canonical_statement_dispatch() {
    let (green, _) = run_statement("act A with {}");
    assert_eq!(green.to_string(), "act A with {}");
    assert_eq!(
        count(&SyntaxNode::new_root(green), SyntaxKind::ActDeclaration),
        1
    );
}
