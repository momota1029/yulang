use crate::tests::support::*;

#[test]
fn error_header_slots_have_direct_rowan_evidence() {
    use SyntaxKind::{Error, Identifier, Missing, Semicolon, Whitespace};

    // BodyIntroducer has no Missing publisher: a clean boundary is Bodyless.
    // These rows select Name before Identifier and BodyIntroducer after it.
    for (tail, expected) in [
        (
            " ;",
            vec![(Whitespace, 0..1), (Missing, 1..1), (Semicolon, 1..2)],
        ),
        (
            " @ ",
            vec![(Whitespace, 0..1), (Error, 1..2), (Whitespace, 2..3)],
        ),
        (
            " $hidden ",
            vec![(Whitespace, 0..1), (Error, 1..8), (Whitespace, 8..9)],
        ),
        (
            " @ 名;",
            vec![
                (Whitespace, 0..1),
                (Error, 1..2),
                (Whitespace, 2..3),
                (Identifier, 3..6),
                (Semicolon, 6..7),
            ],
        ),
        (" 名", vec![(Whitespace, 0..1), (Identifier, 1..4)]),
        (
            " 名 @ ",
            vec![
                (Whitespace, 0..1),
                (Identifier, 1..4),
                (Whitespace, 4..5),
                (Error, 5..6),
                (Whitespace, 6..7),
            ],
        ),
        (
            " 名 @ ;",
            vec![
                (Whitespace, 0..1),
                (Identifier, 1..4),
                (Whitespace, 4..5),
                (Error, 5..6),
                (Whitespace, 6..7),
                (Semicolon, 7..8),
            ],
        ),
        (
            " 名 't @ ;",
            vec![
                (Whitespace, 0..1),
                (Identifier, 1..4),
                (SyntaxKind::DeclarationTypeParameterList, 4..7),
                (Whitespace, 7..8),
                (Error, 8..9),
                (Whitespace, 9..10),
                (Semicolon, 10..11),
            ],
        ),
    ] {
        let source = format!("error{tail}");
        let (green, _, _) = run_error_declaration(&source, 0, 0, LineEntry::InLine, None);
        let root = SyntaxNode::new_root(green);
        let node = root.children().next().expect("direct declaration");
        assert_eq!(node.kind(), SyntaxKind::ErrorDeclaration);
        assert_eq!(node.parent(), Some(root.clone()));
        let children = node.children_with_tokens().collect::<Vec<_>>();
        assert_eq!(children[0].kind(), SyntaxKind::ErrorKw);
        let offset = 5;
        assert_eq!(
            children
                .iter()
                .skip(1)
                .map(|child| (
                    child.kind(),
                    usize::from(child.text_range().start()) - offset
                        ..usize::from(child.text_range().end()) - offset,
                ))
                .collect::<Vec<_>>(),
            expected,
            "{source:?}",
        );
        for child in &children {
            assert_eq!(child.parent(), Some(node.clone()));
            if child.kind() == Missing {
                assert!(child.as_node().is_some());
                assert!(child.text_range().is_empty());
            } else if child.kind() == Error {
                assert!(child.as_token().is_some());
                assert!(!child.text_range().is_empty());
            }
        }
        assert!(
            !root
                .descendants()
                .any(|child| child.kind() == SyntaxKind::Invalid)
        );
    }
}

#[test]
fn error_header_starters_are_outside_name_and_introducer_recovery() {
    use SyntaxKind::{Colon, Equals, Error, Identifier, LBrace, Missing, Semicolon};

    for (body, starter) in [
        (";", Semicolon),
        ("{}", LBrace),
        (":\n  A", Colon),
        ("= A", Equals),
    ] {
        for (header, header_kinds) in [
            (" ", vec![Missing]),
            (" 名 ", vec![Identifier]),
            (" 名 @ ", vec![Identifier, Error]),
        ] {
            let source = format!("error{header}{body}");
            let (green, _, _) = run_error_declaration(&source, 0, 0, LineEntry::InLine, None);
            let root = SyntaxNode::new_root(green);
            let node = root.children().next().expect("direct declaration");
            assert_eq!(node.kind(), SyntaxKind::ErrorDeclaration);
            assert_eq!(node.parent(), Some(root.clone()));
            let children = node.children_with_tokens().collect::<Vec<_>>();
            let at = children
                .iter()
                .position(|child| child.kind() == starter)
                .expect("actual direct starter");
            assert_eq!(
                children
                    .iter()
                    .filter(|child| child.kind() == starter)
                    .count(),
                1,
                "{source:?}",
            );
            assert_eq!(children[at].parent(), Some(node.clone()));
            assert!(children[at].as_token().is_some());
            assert_eq!(
                usize::from(children[at].text_range().start()),
                5 + header.len()
            );
            assert_eq!(
                usize::from(children[at].text_range().end()),
                5 + header.len() + 1
            );
            assert_eq!(
                children[1..at]
                    .iter()
                    .filter(|child| child.kind() != SyntaxKind::Whitespace)
                    .map(|child| child.kind())
                    .collect::<Vec<_>>(),
                header_kinds,
                "{source:?}",
            );
            let expected_recovery = children[1..at]
                .iter()
                .filter(|child| matches!(child.kind(), Missing | Error))
                .cloned()
                .collect::<Vec<_>>();
            assert_eq!(
                root.descendants_with_tokens()
                    .filter(|child| matches!(child.kind(), Missing | Error))
                    .collect::<Vec<_>>(),
                expected_recovery,
                "{source:?}",
            );
            assert!(
                !root
                    .descendants()
                    .any(|child| child.kind() == SyntaxKind::Invalid)
            );
        }
    }
}

#[test]
fn error_braced_variant_outer_close_preserves_protected_boundaries() {
    use crate::lexical::item::{BorrowedTarget, Boundary};
    use crate::lexical::yumark::{FenceOpener, FencePrefixPolicy};
    use SyntaxKind::{
        Comma, EnumVariant, Error, Invalid, LBrace, Missing, StructFieldForeignClose,
    };

    let origin = 100;
    let fence = FenceBoundary {
        opener: FenceOpener {
            line: 0,
            marker: 0..3,
            marker_width: 3,
        },
        prefix_policy: FencePrefixPolicy::ActivePrefixQuote { depth: 2, base: 0 },
        close_column: 0,
    };
    for (accepted, fenced) in [("error E{A", false), ("> > error E{A", true)] {
        let suffix = if fenced {
            "\r\n> > ```\r\nouter"
        } else {
            " \r\n : next"
        };
        let source = format!("{accepted}{suffix}");
        let (green, exit, remainder) = run_error_declaration(
            &source,
            if fenced { 0 } else { STOP_COLON },
            origin,
            if fenced {
                LineEntry::PhysicalStart
            } else {
                LineEntry::InLine
            },
            fenced.then_some(&fence),
        );
        assert_eq!(green.to_string(), accepted, "{source:?}");
        if fenced {
            let Some(NormalizedExit::Complete(
                Err(Either::Left(boundary)),
                LineEntry::PhysicalStart,
            )) = exit
            else {
                panic!("outer close must return the exact fence boundary: {source:?}");
            };
            assert_eq!(remainder, "> > ```\r\nouter");
            let (leading, pending) = emit_terminal_leading_text(boundary);
            assert_eq!(leading, "\r\n");
            assert_eq!(pending.coordinate(), origin + accepted.len() + 2);
            assert!(matches!(
                pending.into_kind(),
                Boundary::BorrowedClose(BorrowedTarget::YumarkFence(_))
            ));
        } else {
            let Some(NormalizedExit::Complete(Err(Either::Left(mut item)), _)) = exit else {
                panic!("active stop must remain pending: {source:?}");
            };
            assert_eq!(item.payload_view().token_kind(), Some(TokenKind::Colon));
            assert_eq!(emit_pending_leading_text(&mut item), " \r\n ");
            assert_eq!(remainder, " next");
        }

        let root = SyntaxNode::new_root(green.clone());
        let node = declaration(&green);
        assert_eq!(root.kind(), SyntaxKind::Root);
        assert_eq!(node.parent(), Some(root.clone()));
        let brace = 7 + if fenced { 4 } else { 0 };
        let mut expected = vec![
            (LBrace, false, brace..brace + 1, "{".to_owned()),
            (EnumVariant, true, brace + 1..brace + 2, "A".to_owned()),
        ];
        if accepted.ends_with(',') {
            expected.push((Comma, false, brace + 2..brace + 3, ",".to_owned()));
        }
        let at = accepted.len();
        expected.push((Missing, true, at..at, String::new()));
        assert_eq!(
            node.children_with_tokens()
                .skip_while(|element| element.kind() != LBrace)
                .map(|element| (
                    element.kind(),
                    element.as_node().is_some(),
                    usize::from(element.text_range().start())
                        ..usize::from(element.text_range().end()),
                    element.to_string(),
                ))
                .collect::<Vec<_>>(),
            expected,
            "{source:?}"
        );
        let missing = root
            .descendants()
            .filter(|node| node.kind() == Missing)
            .collect::<Vec<_>>();
        assert_eq!(missing.len(), 1, "{source:?}");
        assert_eq!(missing[0].parent(), Some(node.clone()));
        assert_eq!(missing[0].children_with_tokens().count(), 0);
        assert_eq!(count(&root, EnumVariant), 1);
        assert!(
            root.descendants_with_tokens().all(|element| !matches!(
                element.kind(),
                Error | Invalid | StructFieldForeignClose
            )),
            "{source:?}"
        );
    }
}

#[test]
fn error_braced_variant_outer_close_has_direct_missing_cst_slot() {
    use SyntaxKind::{
        EnumVariant, Error, Invalid, LBrace, Missing, RBrace, StructFieldForeignClose,
    };

    for (source, accepted, has_variant, closed, foreign) in [
        ("error E{", "error E{", false, false, false),
        ("error E{A", "error E{A", true, false, false),
        ("error E{A}", "error E{A}", true, true, false),
        ("error E{A \r\n )", "error E{A", true, false, true),
    ] {
        let (green, exit, remainder) = run_error_declaration(source, 0, 0, LineEntry::InLine, None);
        assert_eq!(green.to_string(), accepted, "{source:?}");
        assert_eq!(remainder, "", "{source:?}");
        if foreign {
            let Some(NormalizedExit::Complete(Err(Either::Left(mut item)), _)) = exit else {
                panic!("foreign close must remain pending: {source:?}");
            };
            assert_eq!(item.payload_view().token_kind(), Some(TokenKind::RParen));
            assert_eq!(emit_pending_leading_text(&mut item), " \r\n ");
        } else {
            let Some(NormalizedExit::Complete(Err(Either::Right(end)), _)) = exit else {
                panic!("declaration must complete at EOF: {source:?}");
            };
            assert!(end.item.payload_view().is_eof(), "{source:?}");
        }

        let root = SyntaxNode::new_root(green.clone());
        let node = declaration(&green);
        assert_eq!(root.kind(), SyntaxKind::Root);
        assert_eq!(node.parent(), Some(root.clone()), "{source:?}");
        let mut expected = vec![(LBrace, false, 7..8, "{".to_owned())];
        if has_variant {
            expected.push((EnumVariant, true, 8..9, "A".to_owned()));
        }
        let at = 8 + usize::from(has_variant);
        if closed {
            expected.push((RBrace, false, at..at + 1, "}".to_owned()));
        } else {
            expected.push((Missing, true, at..at, String::new()));
        }
        assert_eq!(
            node.children_with_tokens()
                .skip_while(|element| element.kind() != LBrace)
                .map(|element| (
                    element.kind(),
                    element.as_node().is_some(),
                    usize::from(element.text_range().start())
                        ..usize::from(element.text_range().end()),
                    element.to_string(),
                ))
                .collect::<Vec<_>>(),
            expected,
            "{source:?}"
        );
        let missing = root
            .descendants()
            .filter(|node| node.kind() == Missing)
            .collect::<Vec<_>>();
        assert_eq!(missing.len(), usize::from(!closed), "{source:?}");
        for missing in missing {
            assert_eq!(missing.parent(), Some(node.clone()), "{source:?}");
            assert_eq!(missing.children_with_tokens().count(), 0, "{source:?}");
        }
        assert_eq!(count(&root, EnumVariant), usize::from(has_variant));
        assert!(
            root.descendants_with_tokens().all(|element| !matches!(
                element.kind(),
                Error | Invalid | StructFieldForeignClose
            )),
            "{source:?}"
        );
    }
}

#[test]
fn header_recovery_records_are_exact_shifted_and_frozen() {
    use crate::lexical::yumark::{FenceOpener, FencePrefixPolicy};
    use crate::recovery_record::*;
    use std::sync::Arc;
    let fence = FenceBoundary {
        opener: FenceOpener {
            line: 0,
            marker: 0..3,
            marker_width: 3,
        },
        prefix_policy: FencePrefixPolicy::ActivePrefixQuote { depth: 2, base: 0 },
        close_column: 0,
    };
    for (tail, slot, kind, relative) in [
        (
            "\r\n> foreign",
            ErrorDeclarationRole::Name,
            RecoveryKind::Missing,
            2..2,
        ),
        (
            " @\r\n> foreign",
            ErrorDeclarationRole::Name,
            RecoveryKind::Error,
            1..2,
        ),
        (
            " E @\r\n> foreign",
            ErrorDeclarationRole::BodyIntroducer,
            RecoveryKind::Error,
            3..4,
        ),
        (
            " @ \t@  名;",
            ErrorDeclarationRole::Name,
            RecoveryKind::Error,
            1..5,
        ),
        (
            " E @ \t@  ;",
            ErrorDeclarationRole::BodyIntroducer,
            RecoveryKind::Error,
            3..7,
        ),
        (
            " @ \t@\r\n> foreign",
            ErrorDeclarationRole::Name,
            RecoveryKind::Error,
            1..5,
        ),
        (
            " E @ \t@\r\n> foreign",
            ErrorDeclarationRole::BodyIntroducer,
            RecoveryKind::Error,
            3..7,
        ),
        (
            "\r\n> > ```\r\nouter",
            ErrorDeclarationRole::Name,
            RecoveryKind::Missing,
            2..2,
        ),
        (
            " @\r\n> > ```\r\nouter",
            ErrorDeclarationRole::Name,
            RecoveryKind::Error,
            1..2,
        ),
        (
            " E @\r\n> > ```\r\nouter",
            ErrorDeclarationRole::BodyIntroducer,
            RecoveryKind::Error,
            3..4,
        ),
        (
            "  ]",
            ErrorDeclarationRole::Name,
            RecoveryKind::Missing,
            0..0,
        ),
        (
            "  ",
            ErrorDeclarationRole::Name,
            RecoveryKind::Missing,
            2..2,
        ),
        (" @ ", ErrorDeclarationRole::Name, RecoveryKind::Error, 1..2),
        (
            " @  ]",
            ErrorDeclarationRole::Name,
            RecoveryKind::Error,
            1..2,
        ),
        (
            " @ 名;",
            ErrorDeclarationRole::Name,
            RecoveryKind::Error,
            1..2,
        ),
        (
            " ;",
            ErrorDeclarationRole::Name,
            RecoveryKind::Missing,
            1..1,
        ),
        (
            " {}",
            ErrorDeclarationRole::Name,
            RecoveryKind::Missing,
            1..1,
        ),
        (
            " = A",
            ErrorDeclarationRole::Name,
            RecoveryKind::Missing,
            1..1,
        ),
        (
            " :\n  A",
            ErrorDeclarationRole::Name,
            RecoveryKind::Missing,
            1..1,
        ),
        (
            " E @ ",
            ErrorDeclarationRole::BodyIntroducer,
            RecoveryKind::Error,
            3..4,
        ),
        (
            " E @  ]",
            ErrorDeclarationRole::BodyIntroducer,
            RecoveryKind::Error,
            3..4,
        ),
        (
            " E @ ;",
            ErrorDeclarationRole::BodyIntroducer,
            RecoveryKind::Error,
            3..4,
        ),
        (
            " E @ {}",
            ErrorDeclarationRole::BodyIntroducer,
            RecoveryKind::Error,
            3..4,
        ),
        (
            " E @ = A",
            ErrorDeclarationRole::BodyIntroducer,
            RecoveryKind::Error,
            3..4,
        ),
        (
            " E @ :\n  A",
            ErrorDeclarationRole::BodyIntroducer,
            RecoveryKind::Error,
            3..4,
        ),
    ] {
        let source = format!("error{tail}");
        for origin in [0, 1700] {
            let range = origin + 5 + relative.start..origin + 5 + relative.end;
            let role = GrammarRole::Declaration(DeclarationRole::Error(slot));
            let expected: Vec<_> = if slot == ErrorDeclarationRole::Name {
                vec![ExpectedSyntax::Identifier]
            } else {
                vec![
                    ExpectedSyntax::Punctuation(PunctuationEvidence::Semicolon),
                    ExpectedSyntax::Punctuation(PunctuationEvidence::Open(Delimiter::Brace)),
                    ExpectedSyntax::Punctuation(PunctuationEvidence::Colon),
                    ExpectedSyntax::Punctuation(PunctuationEvidence::Equals),
                ]
            };
            let record = CommittedRecoveryRecord {
                id: DiagnosticId(0),
                site: RecoverySiteKey {
                    role,
                    range: range.clone(),
                },
                kind,
                unexpected: if kind == RecoveryKind::Missing {
                    Arc::from([])
                } else if source.contains("@ \t@") {
                    Arc::from([
                        UnexpectedSyntax::Token {
                            range: range.start..range.start + 1,
                            category: UnexpectedCategory::OtherCharacter,
                        },
                        UnexpectedSyntax::Token {
                            range: range.start + 1..range.end,
                            category: UnexpectedCategory::OtherCharacter,
                        },
                    ])
                } else {
                    Arc::from([UnexpectedSyntax::Token {
                        range: range.clone(),
                        category: UnexpectedCategory::OtherCharacter,
                    }])
                },
                expectations: expected
                    .into_iter()
                    .map(|expected| SyntaxExpectation {
                        role,
                        expected,
                        range: range.clone(),
                        sources: ExpectationSources::COMMITTED_RECOVERY_RULE,
                    })
                    .collect(),
                primary_expectation: 0,
            };
            for mode in 0..3 {
                let mut seed = record.clone();
                seed.id = DiagnosticId(7);
                seed.site.range = 0..0;
                seed.kind = RecoveryKind::Missing;
                seed.unexpected = Arc::from([]);
                seed.expectations = seed
                    .expectations
                    .iter()
                    .cloned()
                    .map(|mut e| {
                        e.range = 0..0;
                        e
                    })
                    .collect();
                let mut reused = record.clone();
                if mode == 2 {
                    reused.id = DiagnosticId(19);
                }
                let records = if mode == 2 {
                    vec![seed.clone(), reused]
                } else {
                    vec![reused]
                };
                let operators = OperatorTable::empty();
                let mut recover = Recover::new_for_test(&operators);
                let mut output = if mode != 0 {
                    {
                        recover = Recover::reconcile_for_test(recover.operators(), &records);
                        GreenNodeBuilder::new()
                    }
                } else {
                    GreenNodeBuilder::new()
                };
                let mut input = source.as_str();
                output.start_node(SyntaxKind::Root.into());
                if mode == 2 {
                    output.start_node(SyntaxKind::Missing.into());
                    output.finish_node();
                    recover.commit_recovery_for_test(crate::cursor::recovery::RecoveryDraft::new(
                        seed.site,
                        seed.kind,
                        seed.unexpected,
                        seed.expectations,
                        0,
                    ));
                }
                let exit = crate::declaration::error_decl::error_declaration_witness(
                    crate::cursor::SyntaxIn::new(&mut input, &mut recover, &mut output),
                    0,
                    if source.ends_with(']') {
                        stops_for(TokenKind::RBracket)
                    } else {
                        0
                    },
                    crate::statement::StatementLineHandoff::OrdinaryLayout,
                    origin,
                    LineEntry::InLine,
                    source.contains("\r\n>").then_some(&fence),
                );
                output.finish_node();
                let (green, actual) = (output.finish(), recover.finish_recoveries_for_test());
                assert_eq!(actual, records, "{source:?}");
                if source.contains("@ \t@") {
                    let node = declaration(&green);
                    let errors: Vec<_> = crate::tests::recovery_output::recovery_groups(&node)
                        .into_iter()
                        .collect();
                    assert_eq!(errors.len(), 1);
                    assert_eq!(errors[0].to_string(), "@ \t@");
                    assert_eq!(
                        errors[0]
                            .children_with_tokens()
                            .map(|leaf| (leaf.kind(), leaf.to_string()))
                            .collect::<Vec<_>>(),
                        [
                            (SyntaxKind::Error, "@".into()),
                            (SyntaxKind::Error, " \t".into()),
                            (SyntaxKind::Error, "@".into())
                        ]
                    );
                    assert_eq!(count(&node, SyntaxKind::Missing), 0);
                }
                if let Some((head, tail)) = source.split_once("\r\n>") {
                    let Some(NormalizedExit::Complete(
                        Err(Either::Left(boundary)),
                        LineEntry::PhysicalStart,
                    )) = exit
                    else {
                        panic!("fence boundary")
                    };
                    assert_eq!(green.to_string(), head);
                    assert_eq!(input, format!(">{tail}"));
                    let (leading, boundary) = emit_terminal_leading_text(boundary);
                    assert_eq!(leading, "\r\n");
                    assert_eq!(boundary.coordinate(), origin + head.len() + 2);
                } else if source.ends_with(']') {
                    pending_token(exit, TokenKind::RBracket, "  ");
                } else {
                    assert_eq!(green.to_string(), source, "{source:?}");
                }
            }
        }
    }
}

fn declaration(green: &GreenNode) -> SyntaxNode {
    SyntaxNode::new_root(green.clone())
        .descendants()
        .find(|node| node.kind() == SyntaxKind::ErrorDeclaration)
        .expect("ErrorDeclaration")
}

#[test]
fn clean_header_keeps_foreign_prefix_without_body_introducer_recovery() {
    use crate::lexical::yumark::{FenceOpener, FencePrefixPolicy};
    use crate::recovery_record::*;
    use std::sync::Arc;
    let role = GrammarRole::Declaration(DeclarationRole::Error(ErrorDeclarationRole::Name));
    let seed = CommittedRecoveryRecord {
        id: DiagnosticId(7),
        site: RecoverySiteKey { role, range: 0..0 },
        kind: RecoveryKind::Missing,
        unexpected: Arc::from([]),
        expectations: Arc::from([SyntaxExpectation {
            role,
            expected: ExpectedSyntax::Identifier,
            range: 0..0,
            sources: ExpectationSources::COMMITTED_RECOVERY_RULE,
        }]),
        primary_expectation: 0,
    };
    let fence = FenceBoundary {
        opener: FenceOpener {
            line: 0,
            marker: 0..3,
            marker_width: 3,
        },
        prefix_policy: FencePrefixPolicy::ActivePrefixQuote { depth: 2, base: 0 },
        close_column: 0,
    };
    for origin in [0, 1700] {
        for mode in 0..3 {
            let source = "error 名\r\n> foreign";
            let mut input = source;
            let operators = OperatorTable::empty();
            let mut recover = Recover::new_for_test(&operators);
            let expected = if mode == 2 {
                vec![seed.clone()]
            } else {
                vec![]
            };
            let mut output = if mode != 0 {
                {
                    recover = Recover::reconcile_for_test(recover.operators(), &expected);
                    GreenNodeBuilder::new()
                }
            } else {
                GreenNodeBuilder::new()
            };
            output.start_node(SyntaxKind::Root.into());
            if mode == 2 {
                output.start_node(SyntaxKind::Missing.into());
                output.finish_node();
                recover.commit_recovery_for_test(crate::cursor::recovery::RecoveryDraft::new(
                    seed.site.clone(),
                    seed.kind,
                    seed.unexpected.clone(),
                    seed.expectations.clone(),
                    0,
                ));
            }
            let exit = crate::declaration::error_decl::error_declaration_witness(
                crate::cursor::SyntaxIn::new(&mut input, &mut recover, &mut output),
                0,
                0,
                crate::statement::StatementLineHandoff::OrdinaryLayout,
                origin,
                LineEntry::InLine,
                Some(&fence),
            );
            output.finish_node();
            let (green, records) = (output.finish(), recover.finish_recoveries_for_test());
            assert_eq!(records, expected);
            assert_eq!(green.to_string(), "error 名");
            assert_eq!(input, "> foreign");
            let Some(NormalizedExit::Complete(Err(Either::Left(item)), LineEntry::PhysicalStart)) =
                exit
            else {
                panic!("foreign prefix remains pending");
            };
            let (leading, boundary) = emit_terminal_leading_text(item);
            assert_eq!(leading, "\r\n");
            assert_eq!(boundary.coordinate(), origin + "error 名\r\n".len());
        }
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

fn pending_token(exit: Option<NormalizedExit>, kind: TokenKind, leading: &str) {
    let mut item = match exit {
        Some(NormalizedExit::Complete(Err(Either::Left(item)), _)) => item,
        Some(NormalizedExit::Complete(Err(Either::Right(end)), _)) => end.item,
        _ => panic!("{kind:?} must remain pending"),
    };
    assert_eq!(item.payload_view().token_kind(), Some(kind));
    assert_eq!(emit_pending_leading_text(&mut item), leading);
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

#[test]
fn error_private_shell_builds_the_shared_variant_surface() {
    for (source, variants) in [
        ("error E", 0),
        ("my error E 't;", 0),
        ("our error E{A, B from T, C{x: U}, D(V), P X Y}", 5),
        ("pub error E:\n  A\n  B", 2),
        ("error E = A | B T", 2),
        ("error E =\n  A\n  | B", 2),
    ] {
        let (green, exit, _) = run_error_declaration(source, 0, 0, LineEntry::InLine, None);
        assert!(exit.is_some(), "{source:?}");
        assert_eq!(green.to_string(), source, "{source:?}");
        let node = declaration(&green);
        assert_eq!(
            count(&node, SyntaxKind::EnumVariant),
            variants,
            "{source:?}"
        );
        assert_eq!(count(&node, SyntaxKind::Error), 0, "{source:?}\n{node:#?}");
    }
}

#[test]
fn error_sigil_head_evidence_recovers_one_maximal_raw_name_and_stops() {
    let source = "my error &hidden = A";
    let (green, exit, remainder) = run_error_declaration(source, 0, 0, LineEntry::InLine, None);
    assert_eq!(green.to_string(), "my error &hidden");
    assert_eq!(remainder, " A");
    pending_token(exit, TokenKind::Equals, " ");
    let node = declaration(&green);
    assert_eq!(count(&node, SyntaxKind::Error), 1, "{node:#?}");
    assert_eq!(count(&node, SyntaxKind::Missing), 0, "{node:#?}");
    assert_eq!(count(&node, SyntaxKind::EnumVariant), 0, "{node:#?}");
    assert_eq!(count(&node, SyntaxKind::DerivesClause), 0, "{node:#?}");
    assert_eq!(token_count(&node, SyntaxKind::Identifier), 0, "{node:#?}");
    assert_eq!(token_count(&node, SyntaxKind::Equals), 0, "{node:#?}");
    let error = crate::tests::recovery_output::recovery_groups(&node)
        .into_iter()
        .next()
        .expect("one declaration-local Name Error");
    assert_eq!(error.text().to_string(), "&hidden");
}

#[test]
fn error_sigil_name_error_retries_one_raw_identifier() {
    let source = "my error $hidden E = A";
    let (green, exit, remainder) = run_error_declaration(source, 0, 0, LineEntry::InLine, None);
    assert!(exit.is_some());
    assert_eq!(green.to_string(), source);
    assert_eq!(remainder, "");
    let node = declaration(&green);
    assert_eq!(count(&node, SyntaxKind::Error), 1, "{node:#?}");
    assert_eq!(count(&node, SyntaxKind::Missing), 0, "{node:#?}");
    assert_eq!(count(&node, SyntaxKind::EnumVariant), 1, "{node:#?}");
    assert_eq!(token_count(&node, SyntaxKind::Identifier), 2, "{node:#?}");
}

#[test]
fn error_header_and_actual_brace_close_attach_companions() {
    for source in [
        "error E with {}",
        "error E derives Eq with {}",
        "error E{} derives Eq with {}",
        "error E{@, A} derives Eq with {}",
        "error E{A from } derives Eq with {}",
    ] {
        let (green, _, _) = run_error_declaration(source, 0, 0, LineEntry::InLine, None);
        assert_eq!(green.to_string(), source, "{source:?}");
        assert_eq!(
            count(&declaration(&green), SyntaxKind::DeclarationCompanion),
            1
        );
    }
}

#[test]
fn error_header_derives_recovery_hands_the_exact_with_to_companion() {
    for (source, missing, errors) in [
        ("error E derives with {}", 1, 0),
        ("error E derives @ Eq with {}", 0, 1),
    ] {
        let (green, _, remainder) = run_error_declaration(source, 0, 0, LineEntry::InLine, None);
        assert_eq!(green.to_string(), source, "{source:?}");
        assert_eq!(remainder, "", "{source:?}");
        let node = declaration(&green);
        assert_eq!(count(&node, SyntaxKind::DerivesClause), 1, "{source:?}");
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
            count(&node, SyntaxKind::DeclarationCompanion),
            1,
            "{source:?}\n{node:#?}",
        );
    }
}

#[test]
fn error_equals_inline_returns_the_same_with_to_outer_statement() {
    for (source, accepted, missing) in [
        ("error E = A with {}", "error E = A", 0),
        ("error E = with {}", "error E =", 1),
        ("error E = A | with {}", "error E = A |", 0),
        ("error E = A from with {}", "error E = A from", 1),
        ("error E = A from @ with {}", "error E = A from @", 0),
    ] {
        let (green, exit, _) = run_error_declaration(source, 0, 0, LineEntry::InLine, None);
        assert_eq!(green.to_string(), accepted, "{source:?}");
        let node = declaration(&green);
        assert_eq!(
            count(&node, SyntaxKind::DeclarationCompanion),
            0,
            "{source:?}"
        );
        assert_eq!(
            count(&node, SyntaxKind::Missing),
            missing,
            "{source:?}\n{node:#?}"
        );
        pending_word(exit, "with", " ");
    }
}

#[test]
fn error_equals_inline_yields_with_only_after_a_qualifying_gap() {
    let source = "error E=with";
    let (green, exit, remainder) = run_error_declaration(source, 0, 0, LineEntry::InLine, None);
    assert_eq!(green.to_string(), source);
    assert_eq!(remainder, "");
    assert!(exit.is_some());
    let node = declaration(&green);
    assert_eq!(count(&node, SyntaxKind::EnumVariant), 1);
    assert_eq!(count(&node, SyntaxKind::DeclarationCompanion), 0);
    assert_eq!(count(&node, SyntaxKind::Missing), 0, "{node:#?}");
    assert_eq!(count(&node, SyntaxKind::Error), 0, "{node:#?}");

    let source = "error E = A\n  with {}";
    let (green, exit, remainder) = run_error_declaration(source, 0, 0, LineEntry::InLine, None);
    assert_eq!(green.to_string(), "error E = A");
    assert_eq!(remainder, " {}");
    pending_word(exit, "with", "\n  ");
}

#[test]
fn error_equals_inline_caller_stop_wins_before_the_shared_with_yield() {
    let source = "error E = A |  with {}";
    let (green, exit, remainder) = run_error_declaration(
        source,
        crate::lexical::stops::STOP_WITH,
        0,
        LineEntry::InLine,
        None,
    );
    assert_eq!(green.to_string(), "error E = A |");
    assert_eq!(remainder, " {}");
    let node = declaration(&green);
    assert_eq!(count(&node, SyntaxKind::DeclarationCompanion), 0);
    assert_eq!(count(&node, SyntaxKind::Missing), 0, "{node:#?}");
    pending_word(exit, "with", "  ");
}

#[test]
fn enum_and_error_my_intro_keep_the_binding_collision_private() {
    for source in ["my enum = value", "my error = value"] {
        let (_, exit, remainder) = if source.contains("enum") {
            run_enum_declaration(source, 0, 0, LineEntry::InLine, None)
        } else {
            run_error_declaration(source, 0, 0, LineEntry::InLine, None)
        };
        assert!(exit.is_none(), "{source:?}");
        assert_eq!(remainder, source, "{source:?}");
    }
}

#[test]
fn error_brace_trailing_requires_the_actual_matching_close() {
    for (source, accepted, pending, leading) in [
        ("error E; with {}", "error E;", Some("with"), " "),
        (
            "error E:\n  A\nwith {}",
            "error E:\n  A",
            Some("with"),
            "\n",
        ),
        (
            "error E =\n  A\nwith {}",
            "error E =\n  A",
            Some("with"),
            "\n",
        ),
        ("error E{A with {}", "error E{A with {}", None, ""),
        ("error E{A] with {}", "error E{A", Some("]"), ""),
    ] {
        let (green, exit, _) = run_error_declaration(source, 0, 0, LineEntry::InLine, None);
        assert_eq!(green.to_string(), accepted, "{source:?}");
        assert_eq!(
            count(&declaration(&green), SyntaxKind::DeclarationCompanion),
            0,
            "{source:?}",
        );
        if let Some(pending) = pending {
            pending_word(exit, pending, leading);
        }
    }
}

#[test]
fn error_equals_inline_yield_preserves_origin_line_entry_and_leading() {
    let origin = 9300;
    let source = "error E = A from @  with {} outer";
    let (green, exit, remainder) =
        run_error_declaration(source, 0, origin, LineEntry::InLine, None);
    assert_eq!(green.to_string(), "error E = A from @");
    assert_eq!(remainder, " {} outer");
    let Some(NormalizedExit::Complete(Err(Either::Left(mut item)), LineEntry::InLine)) = exit
    else {
        panic!("Error equals-inline must return the exact shared with Item")
    };
    assert_eq!(item.payload_view().spelling(), Some("with"));
    assert_eq!(emit_pending_leading_text(&mut item), "  ");
    assert_eq!(
        origin + source.len() - remainder.len() - "with".len(),
        origin + "error E = A from @  ".len(),
    );
}

#[test]
fn error_equals_inline_yield_preserves_crlf_fence_handoff() {
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
    let origin = 9500;
    let accepted = "> > error E = A";
    let source = format!("{accepted}\r\n> >   with {{}} outer\r\n> > ```\r\nrest");
    let (green, exit, remainder) =
        run_error_declaration(&source, 0, origin, LineEntry::PhysicalStart, Some(&fence));
    assert_eq!(green.to_string(), accepted);
    assert_eq!(remainder, " {} outer\r\n> > ```\r\nrest");
    let Some(NormalizedExit::Complete(Err(Either::Left(mut item)), LineEntry::InLine)) = exit
    else {
        panic!("Error equals-inline must yield one unchanged fenced with Item")
    };
    assert_eq!(item.payload_view().spelling(), Some("with"));
    assert_eq!(emit_pending_leading_text(&mut item), "\r\n> >   ");
    assert_eq!(
        origin + source.len() - remainder.len() - "with".len(),
        origin + accepted.len() + "\r\n> >   ".len(),
    );
}
