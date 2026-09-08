use super::*;

fn act_record(
    slot: crate::session::ActDeclarationRole,
    kind: crate::session::RecoveryKind,
    range: std::ops::Range<usize>,
) -> CommittedRecoveryRecord {
    use crate::session::*;
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
    use crate::session::{ActDeclarationRole as R, RecoveryKind as K};
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
    use crate::session::{ActDeclarationRole as R, RecoveryKind as K};
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
    use crate::parser::yumark::{FenceOpener, FencePrefixPolicy};
    use crate::session::{ActDeclarationRole as R, RecoveryKind as K};
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
    use crate::session::{ActDeclarationRole as R, BindingRole, DeclarationRole, GrammarRole};
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
    let mut recover = Recover::new(&operators);
    let mut builder = frozen.map_or_else(GreenNodeBuilder::new, GreenNodeBuilder::reconcile);
    builder.start_node(SyntaxKind::Root.into());
    let exit = act_declaration_witness(
        In::new(&mut input, &mut recover, &mut builder),
        0,
        stops,
        super::super::statement::StatementLineHandoff::OrdinaryLayout,
        100,
        LineEntry::InLine,
        fence,
    );
    builder.finish_node();
    let (green, records) = builder.finish_with_recoveries();
    (green, exit, records, input)
}

fn declaration(green: &GreenNode) -> SyntaxNode {
    SyntaxNode::new_root(green.clone())
        .descendants()
        .find(|node| node.kind() == SyntaxKind::ActDeclaration)
        .expect("ActDeclaration")
}

fn count(node: &SyntaxNode, kind: SyntaxKind) -> usize {
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
        super::super::operator::STOP_WITH,
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

    use super::super::item::{BorrowedTarget, Boundary};
    use super::super::yumark::{FenceOpener, FencePrefixPolicy};

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
