use crate::tests::support::*;

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
            EnumDeclarationRole::Name,
            RecoveryKind::Missing,
            2..2,
        ),
        (
            " @\r\n> foreign",
            EnumDeclarationRole::Name,
            RecoveryKind::Error,
            1..2,
        ),
        (
            " E @\r\n> foreign",
            EnumDeclarationRole::BodyIntroducer,
            RecoveryKind::Error,
            3..4,
        ),
        (
            " @ \t@  名;",
            EnumDeclarationRole::Name,
            RecoveryKind::Error,
            1..5,
        ),
        (
            " E @ \t@  ;",
            EnumDeclarationRole::BodyIntroducer,
            RecoveryKind::Error,
            3..7,
        ),
        (
            " @ \t@\r\n> foreign",
            EnumDeclarationRole::Name,
            RecoveryKind::Error,
            1..5,
        ),
        (
            " E @ \t@\r\n> foreign",
            EnumDeclarationRole::BodyIntroducer,
            RecoveryKind::Error,
            3..7,
        ),
        (
            "\r\n> > ```\r\nouter",
            EnumDeclarationRole::Name,
            RecoveryKind::Missing,
            2..2,
        ),
        (
            " @\r\n> > ```\r\nouter",
            EnumDeclarationRole::Name,
            RecoveryKind::Error,
            1..2,
        ),
        (
            " E @\r\n> > ```\r\nouter",
            EnumDeclarationRole::BodyIntroducer,
            RecoveryKind::Error,
            3..4,
        ),
        (
            "  ]",
            EnumDeclarationRole::Name,
            RecoveryKind::Missing,
            0..0,
        ),
        ("  ", EnumDeclarationRole::Name, RecoveryKind::Missing, 2..2),
        (" @ ", EnumDeclarationRole::Name, RecoveryKind::Error, 1..2),
        (
            " @  ]",
            EnumDeclarationRole::Name,
            RecoveryKind::Error,
            1..2,
        ),
        (
            " @ 名;",
            EnumDeclarationRole::Name,
            RecoveryKind::Error,
            1..2,
        ),
        (" ;", EnumDeclarationRole::Name, RecoveryKind::Missing, 1..1),
        (
            " {}",
            EnumDeclarationRole::Name,
            RecoveryKind::Missing,
            1..1,
        ),
        (
            " = A",
            EnumDeclarationRole::Name,
            RecoveryKind::Missing,
            1..1,
        ),
        (
            " :\n  A",
            EnumDeclarationRole::Name,
            RecoveryKind::Missing,
            1..1,
        ),
        (
            " E @ ",
            EnumDeclarationRole::BodyIntroducer,
            RecoveryKind::Error,
            3..4,
        ),
        (
            " E @  ]",
            EnumDeclarationRole::BodyIntroducer,
            RecoveryKind::Error,
            3..4,
        ),
        (
            " E @ ;",
            EnumDeclarationRole::BodyIntroducer,
            RecoveryKind::Error,
            3..4,
        ),
        (
            " E @ {}",
            EnumDeclarationRole::BodyIntroducer,
            RecoveryKind::Error,
            3..4,
        ),
        (
            " E @ = A",
            EnumDeclarationRole::BodyIntroducer,
            RecoveryKind::Error,
            3..4,
        ),
        (
            " E @ :\n  A",
            EnumDeclarationRole::BodyIntroducer,
            RecoveryKind::Error,
            3..4,
        ),
    ] {
        let source = format!("enum{tail}");
        for origin in [0, 1700] {
            let range = origin + 4 + relative.start..origin + 4 + relative.end;
            let role = GrammarRole::Declaration(DeclarationRole::Enum(slot));
            let expected: Vec<_> = if slot == EnumDeclarationRole::Name {
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
                let exit = crate::declaration::enum_decl::enum_declaration_witness(
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
        .find(|node| node.kind() == SyntaxKind::EnumDeclaration)
        .expect("EnumDeclaration")
}

#[test]
fn clean_header_keeps_foreign_prefix_without_body_introducer_recovery() {
    use crate::lexical::yumark::{FenceOpener, FencePrefixPolicy};
    use crate::recovery_record::*;
    use std::sync::Arc;
    let role = GrammarRole::Declaration(DeclarationRole::Enum(EnumDeclarationRole::Name));
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
            let source = "enum 名\r\n> foreign";
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
            let exit = crate::declaration::enum_decl::enum_declaration_witness(
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
            assert_eq!(green.to_string(), "enum 名");
            assert_eq!(input, "> foreign");
            let Some(NormalizedExit::Complete(Err(Either::Left(item)), LineEntry::PhysicalStart)) =
                exit
            else {
                panic!("foreign prefix remains pending");
            };
            let (leading, boundary) = emit_terminal_leading_text(item);
            assert_eq!(leading, "\r\n");
            assert_eq!(boundary.coordinate(), origin + "enum 名\r\n".len());
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
fn enum_private_shell_builds_header_and_all_body_forms() {
    for (source, variants) in [
        ("enum E", 0),
        ("my enum E 't;", 0),
        ("our enum E{A, B from T, C{x: U}, D(V), P X Y}", 5),
        ("pub enum E:\n  A\n  B", 2),
        ("enum E = A | B T", 2),
        ("enum E =\n  A\n  | B", 2),
    ] {
        let (green, exit, _) = run_enum_declaration(source, 0, 0, LineEntry::InLine, None);
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
fn enum_sigil_head_evidence_recovers_one_maximal_raw_name_and_stops() {
    for (source, accepted, malformed) in [
        ("my enum $hidden = A", "my enum $hidden", "$hidden"),
        ("my enum 'hidden = A", "my enum 'hidden", "'hidden"),
    ] {
        let (green, exit, remainder) = run_enum_declaration(source, 0, 0, LineEntry::InLine, None);
        assert_eq!(green.to_string(), accepted, "{source:?}");
        assert_eq!(remainder, " A", "{source:?}");
        pending_token(exit, TokenKind::Equals, " ");
        let node = declaration(&green);
        assert_eq!(count(&node, SyntaxKind::Error), 1, "{source:?}\n{node:#?}");
        assert_eq!(
            count(&node, SyntaxKind::Missing),
            0,
            "{source:?}\n{node:#?}"
        );
        assert_eq!(count(&node, SyntaxKind::EnumVariant), 0, "{source:?}");
        assert_eq!(count(&node, SyntaxKind::DerivesClause), 0, "{source:?}");
        assert_eq!(token_count(&node, SyntaxKind::Identifier), 0, "{source:?}");
        assert_eq!(token_count(&node, SyntaxKind::Equals), 0, "{source:?}");
        let error = crate::tests::recovery_output::recovery_groups(&node)
            .into_iter()
            .next()
            .expect("one declaration-local Name Error");
        assert_eq!(error.text().to_string(), malformed, "{source:?}");
    }
}

#[test]
fn enum_sigil_name_error_retries_one_raw_identifier() {
    let source = "my enum $hidden E = A";
    let (green, exit, remainder) = run_enum_declaration(source, 0, 0, LineEntry::InLine, None);
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
fn enum_header_and_actual_brace_close_attach_in_source_order() {
    for source in [
        "enum E with {}",
        "enum E derives Eq with {}",
        "enum E{} derives Eq with {}",
        "enum E{@, A} derives Eq with {}",
        "enum E{A from } derives Eq with {}",
    ] {
        let (green, _, _) = run_enum_declaration(source, 0, 0, LineEntry::InLine, None);
        assert_eq!(green.to_string(), source, "{source:?}");
        let node = declaration(&green);
        assert_eq!(
            count(&node, SyntaxKind::DeclarationCompanion),
            1,
            "{source:?}"
        );
        assert_eq!(token_count(&node, SyntaxKind::WithKw), 1, "{source:?}");
    }
}

#[test]
fn enum_rejects_trailing_companion_without_an_actual_brace_close() {
    for (source, accepted, pending, leading) in [
        ("enum E; with {}", "enum E;", Some("with"), " "),
        ("enum E:\n  A\nwith {}", "enum E:\n  A", Some("with"), "\n"),
        (
            "enum E =\n  A\nwith {}",
            "enum E =\n  A",
            Some("with"),
            "\n",
        ),
        ("enum E{A with {}", "enum E{A with {}", None, ""),
        ("enum E{A] with {}", "enum E{A", Some("]"), ""),
    ] {
        let (green, exit, _) = run_enum_declaration(source, 0, 0, LineEntry::InLine, None);
        assert_eq!(green.to_string(), accepted, "{source:?}");
        let node = declaration(&green);
        assert_eq!(
            count(&node, SyntaxKind::DeclarationCompanion),
            0,
            "{source:?}"
        );
        if let Some(pending) = pending {
            pending_word(exit, pending, leading);
        }
    }
}

#[test]
fn enum_equals_inline_maps_the_exact_shared_with_yield_to_companion() {
    for (source, missing) in [
        ("enum E = A with {}", 0),
        ("enum E = with {}", 1),
        ("enum E = A | with {}", 0),
        ("enum E = A from with {}", 1),
        ("enum E = A from @ with {}", 0),
    ] {
        let (green, _, _) = run_enum_declaration(source, 0, 0, LineEntry::InLine, None);
        assert_eq!(green.to_string(), source, "{source:?}");
        let node = declaration(&green);
        assert_eq!(
            count(&node, SyntaxKind::DeclarationCompanion),
            1,
            "{source:?}"
        );
        assert_eq!(
            count(&node, SyntaxKind::Missing),
            missing,
            "{source:?}\n{node:#?}"
        );
    }

    let source = "enum E = A from (T with U) with {}";
    let (green, _, _) = run_enum_declaration(source, 0, 0, LineEntry::InLine, None);
    assert_eq!(green.to_string(), source);
    let node = declaration(&green);
    assert_eq!(count(&node, SyntaxKind::DeclarationCompanion), 1);
    assert_eq!(token_count(&node, SyntaxKind::WithKw), 1);
}

#[test]
fn enum_equals_inline_yields_with_only_after_a_qualifying_gap() {
    let source = "enum E=with";
    let (green, exit, remainder) = run_enum_declaration(source, 0, 0, LineEntry::InLine, None);
    assert_eq!(green.to_string(), source);
    assert_eq!(remainder, "");
    assert!(exit.is_some());
    let node = declaration(&green);
    assert_eq!(count(&node, SyntaxKind::EnumVariant), 1);
    assert_eq!(count(&node, SyntaxKind::DeclarationCompanion), 0);
    assert_eq!(count(&node, SyntaxKind::Missing), 0, "{node:#?}");
    assert_eq!(count(&node, SyntaxKind::Error), 0, "{node:#?}");

    let source = "enum E = A\n  with {}";
    let (green, _, _) = run_enum_declaration(source, 0, 0, LineEntry::InLine, None);
    assert_eq!(green.to_string(), source);
    assert_eq!(
        count(&declaration(&green), SyntaxKind::DeclarationCompanion),
        1
    );
}

#[test]
fn enum_equals_inline_caller_stop_wins_before_the_shared_with_yield() {
    let source = "enum E = A |  with {}";
    let (green, exit, remainder) = run_enum_declaration(
        source,
        crate::lexical::stops::STOP_WITH,
        0,
        LineEntry::InLine,
        None,
    );
    assert_eq!(green.to_string(), "enum E = A |");
    assert_eq!(remainder, " {}");
    let node = declaration(&green);
    assert_eq!(count(&node, SyntaxKind::DeclarationCompanion), 0);
    assert_eq!(count(&node, SyntaxKind::Missing), 0, "{node:#?}");
    pending_word(exit, "with", "  ");
}

#[test]
fn enum_caller_stop_and_rejected_gap_keep_with_pending() {
    let (green, exit, _) = run_enum_declaration(
        "enum E = A with {}",
        crate::lexical::stops::STOP_WITH,
        0,
        LineEntry::InLine,
        None,
    );
    assert_eq!(
        count(&declaration(&green), SyntaxKind::DeclarationCompanion),
        0
    );
    pending_word(exit, "with", " ");

    for (source, leading) in [("enum E\nwith {}", "\n"), ("enum E{}\nwith {}", "\n")] {
        let (green, exit, _) = run_enum_declaration(source, 0, 0, LineEntry::InLine, None);
        assert_eq!(
            count(&declaration(&green), SyntaxKind::DeclarationCompanion),
            0
        );
        pending_word(exit, "with", leading);
    }
}

#[test]
fn enum_header_derives_returns_variant_body_starters_by_outer_phase() {
    for (source, variants) in [
        ("enum E derives {}", 0),
        ("enum E derives :\n  A", 1),
        ("enum E derives = A", 1),
        ("enum E derives ;", 0),
        ("enum E derives Eq{}", 0),
        ("enum E derives Eq:\n  A", 1),
        ("enum E derives Eq = A", 1),
        ("enum E derives Eq;", 0),
    ] {
        let (green, _, _) = run_enum_declaration(source, 0, 0, LineEntry::InLine, None);
        assert_eq!(green.to_string(), source, "{source:?}");
        let node = declaration(&green);
        assert_eq!(count(&node, SyntaxKind::DerivesClause), 1, "{source:?}");
        assert_eq!(
            count(&node, SyntaxKind::EnumVariant),
            variants,
            "{source:?}"
        );
    }

    let source = "enum E derives (Eq with T) with {}";
    let (green, _, _) = run_enum_declaration(source, 0, 0, LineEntry::InLine, None);
    assert_eq!(green.to_string(), source);
    let node = declaration(&green);
    assert_eq!(count(&node, SyntaxKind::DeclarationCompanion), 1);
    assert_eq!(token_count(&node, SyntaxKind::WithKw), 1);
}

#[test]
fn enum_header_derives_recovery_hands_the_exact_with_to_companion() {
    for (source, missing, errors) in [
        ("enum E derives with {}", 1, 0),
        ("enum E derives @ Eq with {}", 0, 1),
    ] {
        let (green, _, remainder) = run_enum_declaration(source, 0, 0, LineEntry::InLine, None);
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
        assert_eq!(token_count(&node, SyntaxKind::WithKw), 1, "{source:?}");
    }
}

#[test]
fn enum_companion_keeps_exact_outer_remainder_and_fence_boundary() {
    let origin = 9100;
    let declaration_text = "enum E = A with {}";
    let source = format!("{declaration_text} outer tail");
    let (green, exit, remainder) =
        run_enum_declaration(&source, 0, origin, LineEntry::InLine, None);
    assert!(matches!(
        exit,
        Some(NormalizedExit::Complete(Ok(()), LineEntry::InLine))
    ));
    assert_eq!(green.to_string(), declaration_text);
    assert_eq!(remainder, " outer tail");

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
    let accepted = "> > enum E{} with: our x = y";
    let source = format!("{accepted}\r\n> > ```\r\nouter");
    let (green, exit, remainder) =
        run_enum_declaration(&source, 0, origin, LineEntry::PhysicalStart, Some(&fence));
    let Some(NormalizedExit::Complete(Err(Either::Left(boundary)), LineEntry::PhysicalStart)) =
        exit
    else {
        panic!("Enum companion must return the exact fence boundary")
    };
    assert_eq!(green.to_string(), accepted);
    assert_eq!(remainder, "> > ```\r\nouter");
    let (leading, pending) = emit_terminal_leading_text(boundary);
    assert_eq!(leading, "\r\n");
    assert_eq!(pending.coordinate(), origin + accepted.len() + 2);
    assert!(matches!(
        pending.into_kind(),
        Boundary::BorrowedClose(BorrowedTarget::YumarkFence(_))
    ));
}

#[test]
fn enum_equals_inline_companion_preserves_crlf_fence_origin_and_line_entry() {
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
    let origin = 9400;
    let accepted = "> > enum E = A\r\n> >   with: our x = y";
    let source = format!("{accepted}\r\n> > ```\r\nouter");
    let (green, exit, remainder) =
        run_enum_declaration(&source, 0, origin, LineEntry::PhysicalStart, Some(&fence));
    let Some(NormalizedExit::Complete(Err(Either::Left(boundary)), LineEntry::PhysicalStart)) =
        exit
    else {
        panic!("Enum equals-inline companion must return the exact fence boundary")
    };
    assert_eq!(green.to_string(), accepted);
    assert_eq!(remainder, "> > ```\r\nouter");
    assert_eq!(
        count(&declaration(&green), SyntaxKind::DeclarationCompanion),
        1
    );
    let (leading, pending) = emit_terminal_leading_text(boundary);
    assert_eq!(leading, "\r\n");
    assert_eq!(pending.coordinate(), origin + accepted.len() + 2);
    assert!(matches!(
        pending.into_kind(),
        Boundary::BorrowedClose(BorrowedTarget::YumarkFence(_))
    ));
}
