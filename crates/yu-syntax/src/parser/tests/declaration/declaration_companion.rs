use crate::parser::tests::support::*;
use crate::session::{
    ConstructRole, DeclarationCompanionRole as CompanionRole, DeclarationRole, Delimiter,
    DiagnosticId, ExpectationSources, ExpectedSyntax, GrammarRole, PunctuationEvidence,
    RecoveryKind, RecoverySiteKey, SyntaxExpectation, UnexpectedCategory, UnexpectedSyntax,
};
use std::sync::Arc;

fn typed_companion<'a>(
    source: &'a str,
    origin: usize,
    stops: Stops,
    fence: Option<&FenceBoundary>,
    frozen: Option<&[CommittedRecoveryRecord]>,
    caller: bool,
) -> (
    GreenNode,
    NormalizedExit,
    &'a str,
    Vec<CommittedRecoveryRecord>,
) {
    let operators = OperatorTable::empty();
    let mut input = source;
    let mut recover = Recover::new(&operators);
    let mut output = frozen.map_or_else(GreenNodeBuilder::new, GreenNodeBuilder::reconcile);
    output.start_node(SyntaxKind::Root.into());
    let i = In::new(&mut input, &mut recover, &mut output);
    let exit = if caller {
        statement_normalized(
            i,
            0,
            stops,
            origin,
            LineEntry::InLine,
            fence,
            Some(crate::parser::context::ambient_claim::AmbientClaimView::root_statement(0)).into(),
            Some(crate::parser::context::sequence::SequenceOwner::RootStatement),
        )
    } else {
        crate::parser::declaration::declaration_companion::declaration_companion_witness(
            i,
            0,
            stops,
            origin,
            LineEntry::InLine,
            fence,
        )
        .expect("selected companion")
    };
    output.finish_node();
    let (green, records) = output.finish_with_recoveries();
    (green, exit, input, records)
}

fn companion_record(
    role: GrammarRole,
    kind: RecoveryKind,
    range: std::ops::Range<usize>,
    unexpected: Option<UnexpectedCategory>,
) -> CommittedRecoveryRecord {
    let expected = match role {
        GrammarRole::Declaration(DeclarationRole::Companion(CompanionRole::Introducer)) => {
            ExpectedSyntax::Punctuation(PunctuationEvidence::Colon)
        }
        GrammarRole::Declaration(DeclarationRole::Companion(CompanionRole::Separator)) => {
            ExpectedSyntax::StatementSeparator
        }
        GrammarRole::ClosingDelimiter { delimiter, .. } => {
            ExpectedSyntax::Punctuation(PunctuationEvidence::Close(delimiter))
        }
        _ => ExpectedSyntax::Statement,
    };
    CommittedRecoveryRecord {
        id: DiagnosticId(0),
        site: RecoverySiteKey {
            role,
            range: range.clone(),
        },
        kind,
        unexpected: unexpected.map_or_else(
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

#[test]
fn companion_publication_has_exact_shifted_and_frozen_records() {
    for (source, role, kind, range) in [
        (
            "with  ",
            CompanionRole::Introducer,
            RecoveryKind::Missing,
            106..106,
        ),
        (
            "with item",
            CompanionRole::Introducer,
            RecoveryKind::Missing,
            105..105,
        ),
        (
            "with :: item",
            CompanionRole::Introducer,
            RecoveryKind::Error,
            105..106,
        ),
        (
            "with:  ",
            CompanionRole::Body,
            RecoveryKind::Missing,
            107..107,
        ),
        (
            "with: @ @ item",
            CompanionRole::Body,
            RecoveryKind::Error,
            106..109,
        ),
        (
            "with { @ @ item }",
            CompanionRole::Item,
            RecoveryKind::Error,
            107..110,
        ),
        (
            "with:\r\n  @ @ item",
            CompanionRole::IndentedItem,
            RecoveryKind::Error,
            109..112,
        ),
        (
            "with {,}",
            CompanionRole::Item,
            RecoveryKind::Missing,
            106..106,
        ),
        (
            "with { struct S{} type T = Int }",
            CompanionRole::Separator,
            RecoveryKind::Missing,
            117..117,
        ),
    ] {
        let (green, _, _, records) = typed_companion(source, 100, 0, None, None, false);
        let role = GrammarRole::Declaration(DeclarationRole::Companion(role));
        assert_eq!(
            records,
            [companion_record(
                role,
                kind,
                range,
                (kind == RecoveryKind::Error).then_some(UnexpectedCategory::OtherCharacter)
            )],
            "{source:?}"
        );
        let (again, _, _, frozen) = typed_companion(source, 100, 0, None, Some(&records), false);
        assert_eq!(again, green);
        assert_eq!(frozen, records);
    }
}

#[test]
fn companion_errors_keep_retry_and_boundary_leading_outside_the_run() {
    for (source, text, kind, range, leading) in [
        ("with  ]tail", "with", RecoveryKind::Missing, 104..104, "  "),
        (
            "with @  ]tail",
            "with @",
            RecoveryKind::Error,
            105..106,
            "  ",
        ),
        (
            "with @// 日本語\r\n: tail",
            "with @",
            RecoveryKind::Error,
            105..106,
            "// 日本語\r\n",
        ),
    ] {
        let (green, exit, _, records) = typed_companion(source, 100, 0, None, None, false);
        assert_eq!(green.to_string(), text);
        assert_eq!(
            records,
            [companion_record(
                GrammarRole::Declaration(DeclarationRole::Companion(CompanionRole::Introducer)),
                kind,
                range,
                (kind == RecoveryKind::Error).then_some(UnexpectedCategory::OtherCharacter)
            )]
        );
        assert_eq!(emit_pending_leading_text(&mut pending(exit)), leading);
    }
    let (green, _, _, records) = typed_companion(
        "with: @ // 日本語\r\n  derives Role",
        100,
        0,
        None,
        None,
        false,
    );
    let root = syntax_root(green);
    assert_eq!(
        root.descendants()
            .find(|node| node.kind() == SyntaxKind::Error)
            .unwrap()
            .text()
            .to_string(),
        "@"
    );
    assert_eq!(records.len(), 1);
}

#[test]
fn companion_close_records_distinguish_local_error_and_protected_missing() {
    let role = GrammarRole::ClosingDelimiter {
        owner: ConstructRole::DeclarationCompanion,
        delimiter: Delimiter::Brace,
    };
    for (source, stops, kind, range, unexpected) in [
        ("with {  ", 0, RecoveryKind::Missing, 108..108, None),
        (
            "with {  ]tail",
            stops_for(TokenKind::RBracket),
            RecoveryKind::Missing,
            106..106,
            None,
        ),
        (
            "with { ]}",
            0,
            RecoveryKind::Error,
            107..108,
            Some(UnexpectedCategory::Punctuation(PunctuationEvidence::Close(
                Delimiter::Bracket,
            ))),
        ),
    ] {
        let (green, _, _, records) = typed_companion(source, 100, stops, None, None, false);
        assert_eq!(
            records,
            [companion_record(role, kind, range, unexpected)],
            "{source:?}"
        );
        let (again, _, _, frozen) =
            typed_companion(source, 100, stops, None, Some(&records), false);
        assert_eq!(again, green);
        assert_eq!(frozen, records);
    }
    let fence = active_fence();
    for (source, kind, role, range) in [
        (
            "with\r\n>> ```",
            RecoveryKind::Missing,
            GrammarRole::Declaration(DeclarationRole::Companion(CompanionRole::Introducer)),
            106..106,
        ),
        (
            "with: @\r\n>> ```",
            RecoveryKind::Error,
            GrammarRole::Declaration(DeclarationRole::Companion(CompanionRole::Body)),
            106..107,
        ),
        ("with {\r\n>> ```", RecoveryKind::Missing, role, 108..108),
    ] {
        let (green, exit, _, records) = typed_companion(source, 100, 0, Some(&fence), None, false);
        assert!(pending(exit).payload_view().is_boundary());
        assert_eq!(
            records,
            [companion_record(
                role,
                kind,
                range,
                (kind == RecoveryKind::Error).then_some(UnexpectedCategory::OtherCharacter)
            )]
        );
        let (again, _, _, frozen) =
            typed_companion(source, 100, 0, Some(&fence), Some(&records), false);
        assert_eq!(again, green);
        assert_eq!(frozen, records);
    }
}

#[test]
fn companion_records_reach_all_five_declaration_callers() {
    let (green, _, _, records) = typed_companion("error E = A with:", 100, 0, None, None, true);
    assert_eq!(green.to_string(), "error E = A");
    assert!(records.is_empty());
    for source in [
        "struct S{} with:",
        "type T = Int with:",
        "enum E = A with:",
        "error E with:",
        "act A() with:",
    ] {
        let (green, _, _, records) = typed_companion(source, 100, 0, None, None, true);
        let at = 100 + source.len();
        assert_eq!(
            records,
            [companion_record(
                GrammarRole::Declaration(DeclarationRole::Companion(CompanionRole::Body)),
                RecoveryKind::Missing,
                at..at,
                None
            )],
            "{source:?}"
        );
        let (again, _, _, frozen) = typed_companion(source, 100, 0, None, Some(&records), true);
        assert_eq!(again, green);
        assert_eq!(frozen, records);
    }
}

#[test]
fn companion_seeded_reconciliation_keeps_nonpositional_ids_and_nested_roles() {
    let role = GrammarRole::Declaration(DeclarationRole::Companion(CompanionRole::Body));
    let source = "with: @ derives";
    let (_, _, _, nested) = typed_companion(source, 100, 0, None, None, false);
    assert_eq!(nested.len(), 2);
    assert_eq!(
        nested[0],
        companion_record(
            role,
            RecoveryKind::Error,
            106..107,
            Some(UnexpectedCategory::OtherCharacter)
        )
    );
    assert_eq!(
        nested[1].site.role,
        GrammarRole::Declaration(DeclarationRole::Derives(
            crate::session::DerivesRole::RoleReference
        ))
    );
    assert_eq!(nested[1].site.range, 115..115);
    let mut frozen = None;
    let mut first_green = None;
    for pass in 0..2 {
        let operators = OperatorTable::empty();
        let mut input = source;
        let mut recover = Recover::new(&operators);
        let mut builder = frozen
            .as_deref()
            .map_or_else(GreenNodeBuilder::new, GreenNodeBuilder::reconcile);
        builder.start_node(SyntaxKind::Root.into());
        let seed = companion_record(role, RecoveryKind::Missing, 0..0, None);
        builder.start_node(SyntaxKind::Missing.into());
        builder.finish_node();
        builder.commit_recovery(crate::parser::output::RecoveryDraft::new(
            seed.site,
            seed.kind,
            seed.unexpected,
            seed.expectations,
            seed.primary_expectation,
        ));
        crate::parser::declaration::declaration_companion::declaration_companion_witness(
            In::new(&mut input, &mut recover, &mut builder),
            0,
            0,
            100,
            LineEntry::InLine,
            None,
        )
        .unwrap();
        builder.finish_node();
        let (green, mut records) = builder.finish_with_recoveries();
        if pass == 0 {
            let mut expected = vec![companion_record(role, RecoveryKind::Missing, 0..0, None)];
            expected.extend(nested.clone());
            for (index, record) in expected.iter_mut().enumerate() {
                record.id = DiagnosticId(index as u32);
            }
            assert_eq!(records, expected);
            records[0].id = DiagnosticId(7);
            records[1].id = DiagnosticId(13);
            records[2].id = DiagnosticId(29);
            frozen = Some(records);
            first_green = Some(green);
        } else {
            assert_eq!(Some(records), frozen);
            assert_eq!(Some(green), first_green);
        }
    }
}

#[test]
fn companion_separator_keeps_protected_close_leading_and_valid_trailing_slots() {
    for source in [
        "with {item,}",
        "with {item;} ",
        "with {item\r\n}",
        "with:\r\n  item;\r\nouter",
    ] {
        let (_, _, _, records) = typed_companion(source, 100, 0, None, None, false);
        assert!(records.is_empty(), "{source:?}");
    }
    let source = "with {item,  ]tail";
    let (green, exit, remainder, records) = typed_companion(
        source,
        100,
        stops_for(TokenKind::RBracket),
        None,
        None,
        false,
    );
    assert_eq!(green.to_string(), "with {item,");
    assert_eq!(remainder, "tail");
    assert_eq!(emit_pending_leading_text(&mut pending(exit)), "  ");
    assert_eq!(
        records,
        [companion_record(
            GrammarRole::ClosingDelimiter {
                owner: ConstructRole::DeclarationCompanion,
                delimiter: Delimiter::Brace
            },
            RecoveryKind::Missing,
            111..111,
            None
        )]
    );
}

use crate::parser::{
    handoff::Either,
    input::{
        item::{BorrowedTarget, Boundary},
        operator::{STOP_LBRACE, stops_for},
        yumark::{FenceOpener, FencePrefixPolicy},
    },
};

fn syntax_root(green: GreenNode) -> SyntaxNode {
    SyntaxNode::new_root(green)
}

fn count(root: &SyntaxNode, kind: SyntaxKind) -> usize {
    root.descendants()
        .filter(|node| node.kind() == kind)
        .count()
}

fn token_count(root: &SyntaxNode, kind: SyntaxKind) -> usize {
    root.descendants_with_tokens()
        .filter_map(|element| element.into_token())
        .filter(|token| token.kind() == kind)
        .count()
}

fn direct_node_kinds(node: &SyntaxNode) -> Vec<SyntaxKind> {
    node.children().map(|child| child.kind()).collect()
}

fn pending(exit: NormalizedExit) -> Item {
    match exit {
        NormalizedExit::Complete(Err(Either::Left(item)), _) => item,
        NormalizedExit::Complete(Err(Either::Right(end)), _) => end.item,
        _ => panic!("expected one pending companion Item"),
    }
}

fn active_fence() -> FenceBoundary {
    FenceBoundary {
        opener: FenceOpener {
            line: 0,
            marker: 0..3,
            marker_width: 3,
        },
        prefix_policy: FencePrefixPolicy::ActivePrefixQuote { depth: 2, base: 0 },
        close_column: 0,
    }
}

#[test]
fn declaration_companion_witness_requires_the_exact_maximal_word() {
    for source in ["withx: item", "within {item}", "item"] {
        let (green, exit, remainder) =
            run_declaration_companion(source, 0, 0, 0, LineEntry::InLine, None);
        assert!(exit.is_none(), "{source:?}");
        assert_eq!(green.to_string(), "", "{source:?}");
        assert_eq!(remainder, source, "{source:?}");
    }

    let operators = OperatorTable::from_declarations([OperatorDeclaration::new(
        "with",
        OperatorFixities::new().with_infix(BindingPower::scalar(40), BindingPower::scalar(40)),
    )])
    .expect("dynamic contextual-with table");
    let (green, exit, remainder) =
        run_declaration_companion_with("with: item", &operators, 0, 0, 0, LineEntry::InLine, None);
    assert!(exit.is_some());
    assert_eq!(green.to_string(), "with: item");
    assert_eq!(remainder, "");
    let root = syntax_root(green);
    assert_eq!(
        root.descendants_with_tokens()
            .filter_map(|element| element.into_token())
            .filter(|token| token.kind() == SyntaxKind::WithKw)
            .count(),
        1,
    );

    let (green, exit, remainder) =
        run_declaration_companion_with("with?: item", &operators, 0, 0, 0, LineEntry::InLine, None);
    assert!(exit.is_none());
    assert_eq!(green.to_string(), "");
    assert_eq!(remainder, "with?: item");
}

#[test]
fn declaration_companion_builds_each_statement_only_form() {
    for (source, accepted, remainder, statements, indented) in [
        ("with: item;tail", "with: item;", "tail", 1, false),
        (
            "with:\n  first\n  second\nouter",
            "with:\n  first\n  second",
            "",
            2,
            true,
        ),
        (
            "with { first, second }tail",
            "with { first, second }",
            "tail",
            2,
            false,
        ),
        ("with {}tail", "with {}", "tail", 0, false),
    ] {
        let (green, exit, actual_remainder) =
            run_declaration_companion(source, 0, 0, 0, LineEntry::InLine, None);
        assert!(exit.is_some(), "{source:?}");
        assert_eq!(green.to_string(), accepted, "{source:?}");
        assert_eq!(actual_remainder, remainder, "{source:?}");
        let root = syntax_root(green);
        assert_eq!(
            count(&root, SyntaxKind::DeclarationCompanion),
            1,
            "{source:?}"
        );
        assert_eq!(
            count(&root, SyntaxKind::Statement),
            statements,
            "{source:?}"
        );
        assert_eq!(
            count(&root, SyntaxKind::DeclarationCompanionIndentedBody),
            usize::from(indented),
            "{source:?}",
        );
        assert_eq!(count(&root, SyntaxKind::DerivesClause), 0, "{source:?}");
        assert_eq!(count(&root, SyntaxKind::WithBodyTail), 0, "{source:?}");
        assert_eq!(
            count(&root, SyntaxKind::IndentedStatementBlock),
            0,
            "{source:?}"
        );
        assert_eq!(
            count(&root, SyntaxKind::BracedStatementBlockExpression),
            0,
            "{source:?}",
        );
        let companion = root
            .descendants()
            .find(|node| node.kind() == SyntaxKind::DeclarationCompanion)
            .expect("the isolated owner emits one companion");
        let direct = direct_node_kinds(&companion);
        if indented {
            assert_eq!(direct, [SyntaxKind::DeclarationCompanionIndentedBody]);
        } else if statements == 0 {
            assert!(direct.is_empty(), "{source:?}: {direct:?}");
        } else {
            assert_eq!(
                direct
                    .iter()
                    .filter(|&&kind| kind == SyntaxKind::Statement)
                    .count(),
                statements,
                "{source:?}: {direct:?}",
            );
        }
    }

    for source in ["with: derivesx", "with: derives?"] {
        let (green, _, _) = run_declaration_companion(source, 0, 0, 0, LineEntry::InLine, None);
        let root = syntax_root(green);
        assert_eq!(count(&root, SyntaxKind::Statement), 1, "{source:?}");
        assert_eq!(count(&root, SyntaxKind::DerivesClause), 0, "{source:?}");
    }
}

#[test]
fn declaration_companion_derives_run_is_direct_and_precedes_statements() {
    let source = "with: derives Eq derives Ord;tail";
    let (green, exit, remainder) =
        run_declaration_companion(source, 0, 0, 0, LineEntry::InLine, None);
    assert!(matches!(exit, Some(NormalizedExit::Complete(Ok(()), _))));
    assert_eq!(green.to_string(), "with: derives Eq derives Ord;");
    assert_eq!(remainder, "tail");
    let root = syntax_root(green);
    assert_eq!(count(&root, SyntaxKind::DerivesClause), 2, "{root:#?}");
    assert_eq!(count(&root, SyntaxKind::Statement), 0, "{root:#?}");
    let companion = root
        .descendants()
        .find(|node| node.kind() == SyntaxKind::DeclarationCompanion)
        .expect("one declaration companion");
    assert_eq!(
        direct_node_kinds(&companion),
        [SyntaxKind::DerivesClause, SyntaxKind::DerivesClause],
    );
    assert_eq!(count(&root, SyntaxKind::WithBodyTail), 0);
    assert_eq!(count(&root, SyntaxKind::IndentedStatementBlock), 0);
    assert_eq!(count(&root, SyntaxKind::BracedStatementBlockExpression), 0);
}

#[test]
fn declaration_companion_derives_runs_share_indented_and_braced_sequences() {
    let source = "with:\n  derives Eq derives Ord\n  item\nouter";
    let (green, exit, remainder) =
        run_declaration_companion(source, 0, 0, 0, LineEntry::InLine, None);
    assert_eq!(green.to_string(), "with:\n  derives Eq derives Ord\n  item");
    assert_eq!(remainder, "");
    let mut outer = pending(exit.expect("indented companion returns its dedent Item"));
    assert_eq!(outer.payload_view().spelling(), Some("outer"));
    assert_eq!(emit_pending_leading_text(&mut outer), "\n");
    let root = syntax_root(green);
    assert_eq!(count(&root, SyntaxKind::DerivesClause), 2, "{root:#?}");
    assert_eq!(count(&root, SyntaxKind::Statement), 1, "{root:#?}");
    let body = root
        .descendants()
        .find(|node| node.kind() == SyntaxKind::DeclarationCompanionIndentedBody)
        .expect("one indented companion body");
    assert_eq!(
        direct_node_kinds(&body),
        [
            SyntaxKind::DerivesClause,
            SyntaxKind::DerivesClause,
            SyntaxKind::BlockStatementSeparator,
            SyntaxKind::Statement,
        ],
    );

    let source = "with { derives Eq derives Ord; item }tail";
    let (green, exit, remainder) =
        run_declaration_companion(source, 0, 0, 0, LineEntry::InLine, None);
    assert!(matches!(exit, Some(NormalizedExit::Complete(Ok(()), _))));
    assert_eq!(green.to_string(), "with { derives Eq derives Ord; item }");
    assert_eq!(remainder, "tail");
    let root = syntax_root(green);
    assert_eq!(count(&root, SyntaxKind::DerivesClause), 2, "{root:#?}");
    assert_eq!(count(&root, SyntaxKind::Statement), 1, "{root:#?}");
    assert_eq!(count(&root, SyntaxKind::BlockStatementSeparator), 1);
    let companion = root
        .descendants()
        .find(|node| node.kind() == SyntaxKind::DeclarationCompanion)
        .expect("one declaration companion");
    assert_eq!(
        direct_node_kinds(&companion),
        [
            SyntaxKind::DerivesClause,
            SyntaxKind::DerivesClause,
            SyntaxKind::BlockStatementSeparator,
            SyntaxKind::Statement,
        ],
    );
}

#[test]
fn declaration_companion_derives_runs_remain_distinct_across_outer_separators() {
    let source = "with:\n  derives Eq\n  derives Ord\nouter";
    let (green, exit, remainder) =
        run_declaration_companion(source, 0, 0, 0, LineEntry::InLine, None);
    assert_eq!(green.to_string(), "with:\n  derives Eq\n  derives Ord");
    assert_eq!(remainder, "");
    let mut outer = pending(exit.expect("indented companion returns its dedent Item"));
    assert_eq!(outer.payload_view().spelling(), Some("outer"));
    assert_eq!(emit_pending_leading_text(&mut outer), "\n");
    let root = syntax_root(green);
    let body = root
        .descendants()
        .find(|node| node.kind() == SyntaxKind::DeclarationCompanionIndentedBody)
        .expect("one indented companion body");
    assert_eq!(
        direct_node_kinds(&body),
        [
            SyntaxKind::DerivesClause,
            SyntaxKind::BlockStatementSeparator,
            SyntaxKind::DerivesClause,
        ],
    );
    assert_eq!(count(&root, SyntaxKind::Statement), 0, "{root:#?}");
    assert_eq!(count(&root, SyntaxKind::Missing), 0, "{root:#?}");

    let source = "with { derives Eq; derives Ord }tail";
    let (green, exit, remainder) =
        run_declaration_companion(source, 0, 0, 0, LineEntry::InLine, None);
    assert!(matches!(exit, Some(NormalizedExit::Complete(Ok(()), _))));
    assert_eq!(green.to_string(), "with { derives Eq; derives Ord }");
    assert_eq!(remainder, "tail");
    let root = syntax_root(green);
    let companion = root
        .descendants()
        .find(|node| node.kind() == SyntaxKind::DeclarationCompanion)
        .expect("one declaration companion");
    assert_eq!(
        direct_node_kinds(&companion),
        [
            SyntaxKind::DerivesClause,
            SyntaxKind::BlockStatementSeparator,
            SyntaxKind::DerivesClause,
        ],
    );
    assert_eq!(count(&root, SyntaxKind::Statement), 0, "{root:#?}");
    assert_eq!(count(&root, SyntaxKind::Missing), 0, "{root:#?}");
}

#[test]
fn declaration_companion_derives_deeper_successor_has_one_sequence_owner() {
    let source = "with:\n  derives Eq via key\n    my enum E = A\nouter";
    let (green, exit, remainder) =
        run_declaration_companion(source, 0, 0, 0, LineEntry::InLine, None);
    assert_eq!(
        green.to_string(),
        "with:\n  derives Eq via key\n    my enum E = A"
    );
    assert_eq!(remainder, "");
    let mut outer = pending(exit.expect("indented companion returns its dedent Item"));
    assert_eq!(outer.payload_view().spelling(), Some("outer"));
    assert_eq!(emit_pending_leading_text(&mut outer), "\n");
    let root = syntax_root(green);
    let body = root
        .descendants()
        .find(|node| node.kind() == SyntaxKind::DeclarationCompanionIndentedBody)
        .expect("one indented companion body");
    assert_eq!(
        direct_node_kinds(&body),
        [
            SyntaxKind::DerivesClause,
            SyntaxKind::Missing,
            SyntaxKind::Statement,
        ],
        "{root:#?}",
    );
    assert_eq!(count(&root, SyntaxKind::Missing), 1, "{root:#?}");
    assert_eq!(count(&root, SyntaxKind::Error), 0, "{root:#?}");
    assert_eq!(count(&root, SyntaxKind::Statement), 1, "{root:#?}");
    assert_eq!(count(&root, SyntaxKind::EnumDeclaration), 1, "{root:#?}");

    let source = "with:\n  derives Eq via key\n    @ item\nouter";
    let (green, exit, remainder) =
        run_declaration_companion(source, 0, 0, 0, LineEntry::InLine, None);
    assert_eq!(green.to_string(), "with:\n  derives Eq via key\n    @ item");
    assert_eq!(remainder, "");
    let mut outer = pending(exit.expect("malformed item still returns its dedent Item"));
    assert_eq!(outer.payload_view().spelling(), Some("outer"));
    assert_eq!(emit_pending_leading_text(&mut outer), "\n");
    let root = syntax_root(green);
    let body = root
        .descendants()
        .find(|node| node.kind() == SyntaxKind::DeclarationCompanionIndentedBody)
        .expect("one indented companion body");
    assert_eq!(
        direct_node_kinds(&body),
        [SyntaxKind::DerivesClause, SyntaxKind::Statement],
        "{root:#?}",
    );
    assert_eq!(count(&root, SyntaxKind::Missing), 0, "{root:#?}");
    assert_eq!(count(&root, SyntaxKind::Error), 1, "{root:#?}");
}

#[test]
fn declaration_companion_derives_deeper_caller_stops_remain_pending() {
    let origin = 7000;
    let accepted = "with:\n  derives Eq via key";
    for (source, stops, spelling, kind) in [
        (
            "with:\n  derives Eq via key\n    else tail",
            STOP_ELSE,
            "else",
            TokenKind::Identifier,
        ),
        (
            "with:\n  derives Eq via key\n    { tail",
            STOP_LBRACE,
            "{",
            TokenKind::LBrace,
        ),
    ] {
        let (green, exit, remainder) =
            run_declaration_companion(source, 0, stops, origin, LineEntry::InLine, None);
        assert_eq!(green.to_string(), accepted, "{source:?}");
        assert_eq!(remainder, " tail", "{source:?}");
        let Some(NormalizedExit::Complete(Err(Either::Left(mut pending)), LineEntry::InLine)) =
            exit
        else {
            panic!("the exact caller stop Item must remain pending: {source:?}")
        };
        assert_eq!(
            pending.payload_view().spelling(),
            Some(spelling),
            "{source:?}"
        );
        assert_eq!(
            pending.payload_view().token_kind(),
            Some(kind),
            "{source:?}"
        );
        assert_eq!(
            emit_pending_leading_text(&mut pending),
            "\n    ",
            "{source:?}"
        );
        let root = syntax_root(green);
        assert_eq!(count(&root, SyntaxKind::DerivesClause), 1, "{root:#?}");
        assert_eq!(count(&root, SyntaxKind::Statement), 0, "{root:#?}");
        assert_eq!(count(&root, SyntaxKind::Missing), 0, "{root:#?}");
        assert_eq!(count(&root, SyntaxKind::Error), 0, "{root:#?}");
    }
}

#[test]
fn declaration_companion_derives_owns_role_commas_and_inner_recovery() {
    let source = "with { derives Eq, Debug; item }tail";
    let (green, exit, remainder) =
        run_declaration_companion(source, 0, 0, 0, LineEntry::InLine, None);
    assert!(matches!(exit, Some(NormalizedExit::Complete(Ok(()), _))));
    assert_eq!(green.to_string(), "with { derives Eq, Debug; item }");
    assert_eq!(remainder, "tail");
    let root = syntax_root(green);
    assert_eq!(count(&root, SyntaxKind::DerivesClause), 1, "{root:#?}");
    assert_eq!(count(&root, SyntaxKind::TypeExpression), 2, "{root:#?}");
    assert_eq!(count(&root, SyntaxKind::Statement), 1, "{root:#?}");
    assert_eq!(count(&root, SyntaxKind::BlockStatementSeparator), 1);
    assert_eq!(count(&root, SyntaxKind::Missing), 0, "{root:#?}");

    let source = "with { derives Eq via key, item }tail";
    let (green, exit, remainder) =
        run_declaration_companion(source, 0, 0, 0, LineEntry::InLine, None);
    assert!(matches!(exit, Some(NormalizedExit::Complete(Ok(()), _))));
    assert_eq!(green.to_string(), "with { derives Eq via key, item }");
    assert_eq!(remainder, "tail");
    let root = syntax_root(green);
    assert_eq!(count(&root, SyntaxKind::DerivesClause), 1, "{root:#?}");
    assert_eq!(count(&root, SyntaxKind::Statement), 1, "{root:#?}");
    assert_eq!(count(&root, SyntaxKind::BlockStatementSeparator), 1);

    for (source, missing, errors) in [
        ("with: derives Eq, via;tail", 2, 0),
        ("with: derives @ Role via @ target;tail", 0, 2),
    ] {
        let (green, _, remainder) =
            run_declaration_companion(source, 0, 0, 0, LineEntry::InLine, None);
        assert_eq!(remainder, "tail", "{source:?}");
        let root = syntax_root(green);
        assert_eq!(count(&root, SyntaxKind::DerivesClause), 1, "{root:#?}");
        assert_eq!(count(&root, SyntaxKind::Statement), 0, "{root:#?}");
        assert_eq!(count(&root, SyntaxKind::Missing), missing, "{root:#?}");
        assert_eq!(count(&root, SyntaxKind::Error), errors, "{root:#?}");
    }
}

#[test]
fn declaration_companion_derives_is_retried_in_every_committed_item_slot() {
    for (source, missing, errors) in [
        ("with derives Eq;tail", 1, 0),
        ("with :: derives Eq;tail", 0, 1),
        ("with { @ derives Eq }tail", 0, 1),
    ] {
        let (green, _, remainder) =
            run_declaration_companion(source, 0, 0, 0, LineEntry::InLine, None);
        assert_eq!(remainder, "tail", "{source:?}");
        let root = syntax_root(green);
        assert_eq!(count(&root, SyntaxKind::DerivesClause), 1, "{root:#?}");
        assert_eq!(count(&root, SyntaxKind::Missing), missing, "{root:#?}");
        assert_eq!(count(&root, SyntaxKind::Error), errors, "{root:#?}");
        let derives = root
            .descendants()
            .find(|node| node.kind() == SyntaxKind::DerivesClause)
            .expect("one direct companion DerivesClause");
        assert!(
            derives
                .ancestors()
                .all(|ancestor| ancestor.kind() != SyntaxKind::Statement),
            "{root:#?}",
        );
    }
}

#[test]
fn declaration_companion_derives_preserves_close_and_caller_handoffs() {
    let (green, exit, remainder) = run_declaration_companion(
        "with { derives Eq]tail",
        0,
        stops_for(TokenKind::RBracket),
        0,
        LineEntry::InLine,
        None,
    );
    assert_eq!(green.to_string(), "with { derives Eq");
    assert_eq!(remainder, "tail");
    let root = syntax_root(green);
    assert_eq!(count(&root, SyntaxKind::DerivesClause), 1, "{root:#?}");
    assert_eq!(count(&root, SyntaxKind::Missing), 1, "{root:#?}");
    assert_eq!(
        pending(exit.expect("caller close remains pending"))
            .payload_view()
            .token_kind(),
        Some(TokenKind::RBracket),
    );

    let (green, exit, remainder) = run_declaration_companion(
        "with { derives Eq : outer",
        0,
        STOP_COLON,
        0,
        LineEntry::InLine,
        None,
    );
    assert_eq!(green.to_string(), "with { derives Eq");
    assert_eq!(remainder, " outer");
    let root = syntax_root(green);
    assert_eq!(count(&root, SyntaxKind::DerivesClause), 1, "{root:#?}");
    assert_eq!(count(&root, SyntaxKind::Missing), 1, "{root:#?}");
    assert_eq!(
        pending(exit.expect("caller stop remains pending"))
            .payload_view()
            .token_kind(),
        Some(TokenKind::Colon),
    );

    let (green, exit, remainder) =
        run_declaration_companion("with { derives Eq) }tail", 0, 0, 0, LineEntry::InLine, None);
    assert!(matches!(exit, Some(NormalizedExit::Complete(Ok(()), _))));
    assert_eq!(remainder, "tail");
    let root = syntax_root(green);
    assert_eq!(count(&root, SyntaxKind::DerivesClause), 1, "{root:#?}");
    assert_eq!(count(&root, SyntaxKind::Error), 1, "{root:#?}");
    assert_eq!(count(&root, SyntaxKind::Missing), 0, "{root:#?}");
}

#[test]
fn declaration_companion_derives_is_identifier_only_and_gate5_stays_closed() {
    let operators = OperatorTable::from_declarations([OperatorDeclaration::new(
        "derives",
        OperatorFixities::new().with_nullfix(),
    )])
    .expect("dynamic derives operator table");
    let (green, _, remainder) = run_declaration_companion_with(
        "with: derives;tail",
        &operators,
        0,
        0,
        0,
        LineEntry::InLine,
        None,
    );
    assert_eq!(remainder, "tail");
    let root = syntax_root(green);
    assert_eq!(count(&root, SyntaxKind::DerivesClause), 0, "{root:#?}");
    assert_eq!(count(&root, SyntaxKind::Statement), 1, "{root:#?}");

    let (green, _, _) = run_declaration_companion(
        "with: derives Eq with Role",
        0,
        0,
        0,
        LineEntry::InLine,
        None,
    );
    let root = syntax_root(green);
    assert_eq!(count(&root, SyntaxKind::DerivesClause), 1, "{root:#?}");
    assert_eq!(token_count(&root, SyntaxKind::WithKw), 1, "{root:#?}");
}

#[test]
fn declaration_companion_introducer_and_body_recovery_retries_once() {
    let (green, exit, remainder) =
        run_declaration_companion("with]tail", 0, 0, 0, LineEntry::InLine, None);
    assert_eq!(green.to_string(), "with");
    assert_eq!(remainder, "tail");
    let root = syntax_root(green);
    assert_eq!(count(&root, SyntaxKind::Missing), 1);
    assert_eq!(count(&root, SyntaxKind::Statement), 0);
    assert_eq!(
        pending(exit.expect("committed companion"))
            .payload_view()
            .token_kind(),
        Some(TokenKind::RBracket),
    );

    for (source, errors) in [("with item", 0), ("with :: item", 1)] {
        let (green, exit, _) = run_declaration_companion(source, 0, 0, 0, LineEntry::InLine, None);
        assert!(exit.is_some(), "{source:?}");
        assert_eq!(green.to_string(), source, "{source:?}");
        let root = syntax_root(green);
        assert_eq!(count(&root, SyntaxKind::Statement), 1, "{source:?}");
        assert_eq!(count(&root, SyntaxKind::Error), errors, "{source:?}");
        assert_eq!(
            count(&root, SyntaxKind::Missing),
            usize::from(errors == 0),
            "{source:?}",
        );
    }

    let source = "with:\nouter";
    let (green, exit, _) = run_declaration_companion(source, 0, 0, 0, LineEntry::InLine, None);
    assert_eq!(green.to_string(), "with:");
    let root = syntax_root(green);
    assert_eq!(count(&root, SyntaxKind::Missing), 1);
    assert_eq!(count(&root, SyntaxKind::Statement), 0);
    let mut item = pending(exit.expect("committed companion"));
    assert_eq!(item.payload_view().spelling(), Some("outer"));
    assert_eq!(emit_pending_leading_text(&mut item), "\n");

    for (source, kind) in [
        ("with: ,tail", TokenKind::Comma),
        ("with: ;tail", TokenKind::Semicolon),
        ("with:\n  ]tail", TokenKind::RBracket),
    ] {
        let (green, exit, remainder) =
            run_declaration_companion(source, 0, 0, 0, LineEntry::InLine, None);
        let root = syntax_root(green);
        assert_eq!(
            count(&root, SyntaxKind::Missing),
            1,
            "{source:?}\n{root:#?}"
        );
        assert_eq!(
            count(&root, SyntaxKind::Statement),
            0,
            "{source:?}\n{root:#?}"
        );
        assert_eq!(
            pending(exit.expect("committed companion"))
                .payload_view()
                .token_kind(),
            Some(kind),
            "{source:?}",
        );
        assert_eq!(remainder, "tail", "{source:?}");
    }

    let (green, exit, remainder) =
        run_declaration_companion("with @ {}tail", 0, 0, 0, LineEntry::InLine, None);
    assert!(matches!(exit, Some(NormalizedExit::Complete(Ok(()), _))));
    assert_eq!(green.to_string(), "with @ {}");
    assert_eq!(remainder, "tail");
    let root = syntax_root(green);
    assert_eq!(count(&root, SyntaxKind::Error), 1, "{root:#?}");
    assert_eq!(count(&root, SyntaxKind::Missing), 0, "{root:#?}");

    let source = "with @// : { item\n: item";
    let (green, exit, remainder) =
        run_declaration_companion(source, 0, 0, 0, LineEntry::InLine, None);
    assert_eq!(green.to_string(), "with @");
    assert_eq!(remainder, " item");
    let root = syntax_root(green);
    assert_eq!(count(&root, SyntaxKind::Error), 1, "{root:#?}");
    assert_eq!(count(&root, SyntaxKind::Missing), 0, "{root:#?}");
    assert_eq!(count(&root, SyntaxKind::Statement), 0, "{root:#?}");
    let mut item = pending(exit.expect("committed companion"));
    assert_eq!(item.payload_view().token_kind(), Some(TokenKind::Colon));
    assert_eq!(emit_pending_leading_text(&mut item), "// : { item\n");
}

#[test]
fn declaration_companion_braced_sequence_owns_only_real_local_slots() {
    let source = "with {,first,,second,}tail";
    let (green, exit, remainder) =
        run_declaration_companion(source, 0, 0, 0, LineEntry::InLine, None);
    assert!(matches!(exit, Some(NormalizedExit::Complete(Ok(()), _))));
    assert_eq!(green.to_string(), "with {,first,,second,}");
    assert_eq!(remainder, "tail");
    let root = syntax_root(green);
    assert_eq!(count(&root, SyntaxKind::Statement), 4, "{root:#?}");
    assert_eq!(count(&root, SyntaxKind::Missing), 2, "{root:#?}");
    assert_eq!(count(&root, SyntaxKind::BlockStatementSeparator), 4);

    let source = "with { struct S{} type T = Int }tail";
    let (green, _, remainder) = run_declaration_companion(source, 0, 0, 0, LineEntry::InLine, None);
    assert_eq!(green.to_string(), "with { struct S{} type T = Int }");
    assert_eq!(remainder, "tail");
    let root = syntax_root(green);
    assert_eq!(count(&root, SyntaxKind::Statement), 2, "{root:#?}");
    assert_eq!(count(&root, SyntaxKind::Missing), 1, "{root:#?}");

    for source in ["with { @ first }tail", "with { @ }tail"] {
        let (green, _, remainder) =
            run_declaration_companion(source, 0, 0, 0, LineEntry::InLine, None);
        assert_eq!(remainder, "tail", "{source:?}");
        let root = syntax_root(green);
        assert_eq!(
            count(&root, SyntaxKind::Statement),
            1,
            "{source:?}\n{root:#?}"
        );
        assert_eq!(count(&root, SyntaxKind::Error), 1, "{source:?}\n{root:#?}");
        assert_eq!(
            count(&root, SyntaxKind::Missing),
            0,
            "{source:?}\n{root:#?}"
        );
    }
}

#[test]
fn declaration_companion_close_and_nested_recovery_keep_their_owner() {
    let (green, exit, _) =
        run_declaration_companion("with { first", 0, 0, 0, LineEntry::InLine, None);
    let root = syntax_root(green);
    assert_eq!(count(&root, SyntaxKind::Missing), 1, "{root:#?}");
    assert!(matches!(
        exit,
        Some(NormalizedExit::Complete(Err(Either::Right(_)), _))
    ));

    let (green, exit, remainder) =
        run_declaration_companion("with { first)}tail", 0, 0, 0, LineEntry::InLine, None);
    assert!(matches!(exit, Some(NormalizedExit::Complete(Ok(()), _))));
    assert_eq!(remainder, "tail");
    let root = syntax_root(green);
    assert_eq!(count(&root, SyntaxKind::Error), 1, "{root:#?}");
    assert_eq!(count(&root, SyntaxKind::Missing), 0, "{root:#?}");

    let (green, exit, remainder) = run_declaration_companion(
        "with { first]tail",
        0,
        stops_for(TokenKind::RBracket),
        0,
        LineEntry::InLine,
        None,
    );
    assert_eq!(green.to_string(), "with { first");
    assert_eq!(remainder, "tail");
    let root = syntax_root(green);
    assert_eq!(count(&root, SyntaxKind::Missing), 1, "{root:#?}");
    assert_eq!(
        pending(exit.expect("committed companion"))
            .payload_view()
            .token_kind(),
        Some(TokenKind::RBracket),
    );

    let (green, _, remainder) =
        run_declaration_companion("with { f(@a) }tail", 0, 0, 0, LineEntry::InLine, None);
    assert_eq!(remainder, "tail");
    let root = syntax_root(green);
    assert_eq!(count(&root, SyntaxKind::Statement), 1, "{root:#?}");
    assert_eq!(count(&root, SyntaxKind::Error), 1, "{root:#?}");
    assert_eq!(count(&root, SyntaxKind::Missing), 0, "{root:#?}");
}

#[test]
fn declaration_companion_braced_body_returns_caller_stops_unchanged() {
    for (source, stops, spelling) in [
        ("with { first : outer", STOP_COLON, ":"),
        ("with { first else outer", STOP_ELSE, "else"),
    ] {
        let (green, exit, remainder) =
            run_declaration_companion(source, 0, stops, 0, LineEntry::InLine, None);
        assert_eq!(green.to_string(), "with { first", "{source:?}");
        assert_eq!(remainder, " outer", "{source:?}");
        let root = syntax_root(green);
        assert_eq!(
            count(&root, SyntaxKind::Statement),
            1,
            "{source:?}\n{root:#?}"
        );
        assert_eq!(
            count(&root, SyntaxKind::Missing),
            1,
            "{source:?}\n{root:#?}"
        );
        assert_eq!(count(&root, SyntaxKind::Error), 0, "{source:?}\n{root:#?}");
        let companion = root
            .descendants()
            .find(|node| node.kind() == SyntaxKind::DeclarationCompanion)
            .expect("the committed owner emits one companion");
        assert_eq!(
            direct_node_kinds(&companion),
            [SyntaxKind::Statement, SyntaxKind::Missing],
            "{source:?}\n{root:#?}",
        );
        let mut item = pending(exit.expect("committed companion"));
        assert_eq!(item.payload_view().spelling(), Some(spelling), "{source:?}");
        assert_eq!(emit_pending_leading_text(&mut item), " ", "{source:?}");
    }
}

#[test]
fn declaration_companion_returns_one_crlf_fence_boundary_item() {
    let fence = active_fence();
    let source = "> > with:\r\n> >   derives Eq\r\n> >   item\r\n> > ```\r\nouter";
    let accepted = "> > with:\r\n> >   derives Eq\r\n> >   item";
    let (green, exit, remainder) =
        run_declaration_companion(source, 0, 0, 900, LineEntry::PhysicalStart, Some(&fence));
    assert_eq!(green.to_string(), accepted);
    assert_eq!(remainder, "> > ```\r\nouter");
    let Some(NormalizedExit::Complete(Err(Either::Left(item)), LineEntry::PhysicalStart)) = exit
    else {
        panic!("the companion must return its exact fence Item")
    };
    let (leading, pending) = emit_terminal_leading_text(item);
    assert_eq!(leading, "\r\n");
    assert!(matches!(
        pending.into_kind(),
        Boundary::BorrowedClose(BorrowedTarget::YumarkFence(_))
    ));
    let root = syntax_root(green);
    assert_eq!(
        count(&root, SyntaxKind::DeclarationCompanionIndentedBody),
        1
    );
    assert_eq!(count(&root, SyntaxKind::Statement), 1);
    assert_eq!(count(&root, SyntaxKind::Missing), 0);
    assert_eq!(count(&root, SyntaxKind::DerivesClause), 1);
}

#[test]
fn declaration_companion_inline_returns_one_crlf_fence_boundary_item() {
    let fence = active_fence();
    let origin = 1200;
    let accepted = "> > with: item";
    let source = format!("{accepted}\r\n> > ```\r\nouter");
    let (green, exit, remainder) = run_declaration_companion(
        &source,
        0,
        0,
        origin,
        LineEntry::PhysicalStart,
        Some(&fence),
    );
    assert_eq!(green.to_string(), accepted);
    assert_eq!(remainder, "> > ```\r\nouter");
    let Some(NormalizedExit::Complete(Err(Either::Left(item)), LineEntry::PhysicalStart)) = exit
    else {
        panic!("the inline companion must return its exact fence Item")
    };
    let (leading, pending) = emit_terminal_leading_text(item);
    assert_eq!(leading, "\r\n");
    assert_eq!(pending.coordinate(), origin + accepted.len() + 2);
    assert!(matches!(
        pending.into_kind(),
        Boundary::BorrowedClose(BorrowedTarget::YumarkFence(_))
    ));
    let root = syntax_root(green);
    assert_eq!(
        count(&root, SyntaxKind::DeclarationCompanionIndentedBody),
        0
    );
    assert_eq!(count(&root, SyntaxKind::Statement), 1);
    assert_eq!(count(&root, SyntaxKind::Missing), 0);
    assert_eq!(count(&root, SyntaxKind::Error), 0);
}
