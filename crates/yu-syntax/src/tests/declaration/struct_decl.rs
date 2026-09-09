use crate::tests::support::*;

fn typed_struct(
    source: &str,
    origin: usize,
    frozen: Option<&[CommittedRecoveryRecord]>,
    stops: Stops,
    fence: Option<&FenceBoundary>,
) -> (GreenNode, NormalizedExit, Vec<CommittedRecoveryRecord>) {
    let (green, exit, records, _) = typed_struct_continuation(source, origin, frozen, stops, fence);
    (green, exit, records)
}

fn typed_struct_continuation<'a>(
    source: &'a str,
    origin: usize,
    frozen: Option<&[CommittedRecoveryRecord]>,
    stops: Stops,
    fence: Option<&FenceBoundary>,
) -> (
    GreenNode,
    NormalizedExit,
    Vec<CommittedRecoveryRecord>,
    &'a str,
) {
    let operators = OperatorTable::empty();
    let mut input = source;
    let mut recover = Recover::new_for_test(&operators);
    let mut builder = frozen.map_or_else(GreenNodeBuilder::new, |records| {
        recover = Recover::reconcile_for_test(recover.operators(), records);
        GreenNodeBuilder::new()
    });
    builder.start_node(SyntaxKind::Root.into());
    let exit = statement_normalized(
        crate::cursor::SyntaxIn::new(&mut input, &mut recover, &mut builder),
        0,
        stops,
        origin,
        LineEntry::InLine,
        fence,
        Some(crate::ambient_claim::AmbientClaimView::root_statement(0)).into(),
        Some(crate::sequence::SequenceOwner::RootStatement),
    );
    builder.finish_node();
    let (green, records) = (builder.finish(), recover.finish_recoveries_for_test());
    (green, exit, records, input)
}

#[test]
fn struct_header_frozen_preserves_exact_close_and_newline_continuation() {
    for header in ["struct", "struct @", "struct S", "struct 名 @"] {
        for (leading, pending, suffix) in [
            ("  ", ")", "tail"),
            ("  ", "}", "tail"),
            ("  ", "]", "tail"),
            ("\r\n", "next", " tail"),
        ] {
            let source = format!("{header}{leading}{pending}{suffix}");
            let (green, exit, mut records, remainder) =
                typed_struct_continuation(&source, 100, None, 0, None);
            assert_eq!(green.to_string(), header);
            assert_eq!(records.len(), 1);
            assert_eq!(remainder, suffix);
            records[0].id = crate::recovery_record::DiagnosticId(71);
            let (again, frozen_exit, frozen, frozen_remainder) =
                typed_struct_continuation(&source, 100, Some(&records), 0, None);
            assert_eq!(again, green);
            assert_eq!(frozen, records);
            assert_eq!(frozen_remainder, remainder);
            let NormalizedExit::Complete(Err(Either::Left(mut item)), entry) = exit else {
                panic!("protected Item")
            };
            let NormalizedExit::Complete(Err(Either::Left(frozen_item)), frozen_entry) =
                frozen_exit
            else {
                panic!("frozen protected Item")
            };
            assert_eq!(frozen_item, item);
            assert_eq!(frozen_entry, entry);
            assert_eq!(entry, LineEntry::InLine);
            let successor_origin = 100 + source.len() - remainder.len();
            assert_eq!(
                successor_origin,
                100 + header.len() + leading.len() + pending.len()
            );
            assert_eq!(
                item.extent(successor_origin).payload(),
                100 + header.len() + leading.len()..successor_origin
            );
            assert_eq!(item.payload_view().spelling(), Some(pending));
            assert_eq!(emit_pending_leading_text(&mut item), leading);
        }
    }
}

#[test]
fn struct_header_visibility_rejection_preserves_seeded_output_and_cursor() {
    use crate::{
        cursor::recovery::RecoveryDraft,
        declaration::struct_decl::struct_declaration_selected_normalized,
        lexical::item::{LeadingTrivia, Payload, Token},
    };
    let (_, _, mut seed) = typed_struct("struct", 100, None, 0, None);
    seed[0].id = crate::recovery_record::DiagnosticId(71);
    for visibility in ["my", "our", "pub"] {
        for source in [" structure S;", "\r\nstruct S;"] {
            let operators = OperatorTable::empty();
            let mut recover = Recover::new_for_test(&operators);
            let mut input = source;
            let mut builder = {
                recover = Recover::reconcile_for_test(recover.operators(), &seed);
                GreenNodeBuilder::new()
            };
            builder.start_node(SyntaxKind::Root.into());
            builder.token(SyntaxKind::Identifier.into(), "seed");
            builder.start_node(SyntaxKind::Missing.into());
            builder.finish_node();
            recover.commit_recovery_for_test(RecoveryDraft::new(
                seed[0].site.clone(),
                seed[0].kind,
                seed[0].unexpected.clone(),
                seed[0].expectations.clone(),
                0,
            ));
            let before = recover.diagnostic_position();
            let make_item = || {
                Item::plain(
                    LeadingTrivia::default(),
                    Payload::Token(Token {
                        kind: TokenKind::Identifier,
                        text: visibility.into(),
                    }),
                )
            };
            let item = make_item();
            assert!(!struct_declaration_selected_normalized(
                crate::cursor::SyntaxIn::new(&mut input, &mut recover, &mut builder),
                &item,
                0,
                100,
                None
            ));
            assert_eq!(item, make_item());
            assert_eq!(input, source);
            assert_eq!(recover.diagnostic_position(), before);
            assert_eq!(recover.recovery_slot_count(), 1);
            builder.finish_node();
            let (green, records) = (builder.finish(), recover.finish_recoveries_for_test());
            assert_eq!(green.to_string(), "seed");
            assert_eq!(
                SyntaxNode::new_root(green).children_with_tokens().count(),
                2
            );
            assert_eq!(records, seed);
        }
    }
}

#[test]
fn struct_header_exact_shifted_frozen_records_and_native_runs() {
    use crate::recovery_record::{
        DeclarationRole, Delimiter, DiagnosticId, ExpectationSources, ExpectedSyntax, GrammarRole,
        PunctuationEvidence, RecoveryKind, RecoverySiteKey, StructRole, SyntaxExpectation,
        UnexpectedCategory, UnexpectedSyntax,
    };
    use std::sync::Arc;
    for (source, slot, kind, range, text) in [
        (
            "struct",
            StructRole::Name,
            RecoveryKind::Missing,
            6..6,
            "struct",
        ),
        (
            "struct  ",
            StructRole::Name,
            RecoveryKind::Missing,
            8..8,
            "struct  ",
        ),
        (
            "struct;",
            StructRole::Name,
            RecoveryKind::Missing,
            6..6,
            "struct;",
        ),
        (
            "struct @ S;",
            StructRole::Name,
            RecoveryKind::Error,
            7..8,
            "struct @ S;",
        ),
        (
            "struct @ # S;",
            StructRole::Name,
            RecoveryKind::Error,
            7..10,
            "struct @ # S;",
        ),
        (
            "struct @  ",
            StructRole::Name,
            RecoveryKind::Error,
            7..8,
            "struct @",
        ),
        (
            "struct S",
            StructRole::BodyIntroducer,
            RecoveryKind::Missing,
            8..8,
            "struct S",
        ),
        (
            "struct S  ",
            StructRole::BodyIntroducer,
            RecoveryKind::Missing,
            10..10,
            "struct S  ",
        ),
        (
            "struct S Foo",
            StructRole::BodyIntroducer,
            RecoveryKind::Missing,
            8..8,
            "struct S ",
        ),
        (
            "struct S @ ;",
            StructRole::BodyIntroducer,
            RecoveryKind::Error,
            9..10,
            "struct S @ ;",
        ),
        (
            "struct S @  ",
            StructRole::BodyIntroducer,
            RecoveryKind::Error,
            9..10,
            "struct S @",
        ),
        (
            "struct 名 @ ;",
            StructRole::BodyIntroducer,
            RecoveryKind::Error,
            11..12,
            "struct 名 @ ;",
        ),
    ] {
        let (green, _, records) = typed_struct(source, 100, None, 0, None);
        assert_eq!(green.to_string(), text, "{source:?}");
        let range = range.start + 100..range.end + 100;
        let role = GrammarRole::Declaration(DeclarationRole::Struct(slot));
        let expected = if slot == StructRole::Name {
            vec![ExpectedSyntax::Identifier]
        } else {
            vec![
                ExpectedSyntax::Punctuation(PunctuationEvidence::Semicolon),
                ExpectedSyntax::Punctuation(PunctuationEvidence::Open(Delimiter::Brace)),
                ExpectedSyntax::Punctuation(PunctuationEvidence::Open(Delimiter::Parenthesis)),
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
        let mut seeded = records.clone();
        seeded[0].id = DiagnosticId(71);
        let (again, _, frozen) = typed_struct(source, 100, Some(&seeded), 0, None);
        assert_eq!(again, green);
        assert_eq!(frozen, seeded);
    }
}

#[test]
fn struct_header_keeps_terminal_leading_and_accepts_deeper_retry() {
    for (source, text) in [
        ("struct  ]tail", "struct"),
        ("struct @  ]tail", "struct @"),
        ("struct S  ]tail", "struct S"),
        ("struct S @  ]tail", "struct S @"),
        ("struct\r\nnext", "struct"),
        ("struct @\r\nnext", "struct @"),
        ("struct S\r\nnext", "struct S"),
        ("struct S @\r\nnext", "struct S @"),
    ] {
        let (green, exit, records) = typed_struct(source, 100, None, 0, None);
        assert_eq!(green.to_string(), text, "{source:?}");
        assert_eq!(records.len(), 1);
        let NormalizedExit::Complete(Err(Either::Left(mut item)), _) = exit else {
            panic!("pending boundary")
        };
        assert!(emit_pending_leading_text(&mut item).len() >= 2);
    }
    for source in [
        "struct @\r\n  S;",
        "struct S @\r\n  ;",
        "struct @ S{}",
        "struct @ S()",
        "struct @ S:\n  x: F",
    ] {
        let (green, _, records) = typed_struct(source, 0, None, 0, None);
        assert_eq!(green.to_string(), source);
        assert_eq!(records.len(), 1);
    }
}

fn declaration(green: &GreenNode) -> SyntaxNode {
    SyntaxNode::new_root(green.clone())
        .descendants()
        .find(|node| node.kind() == SyntaxKind::StructDeclaration)
        .expect("StructDeclaration")
}

#[test]
fn struct_header_active_starters_and_quoted_fences_remain_whole() {
    use crate::lexical::{
        stops::{STOP_COLON, STOP_LBRACE},
        yumark::{FenceOpener, FencePrefixPolicy},
    };
    use crate::recovery_record::RecoveryKind;
    for (source, text, stops, leading) in [
        ("struct  :tail", "struct", STOP_COLON, "  "),
        ("struct @  :tail", "struct @", STOP_COLON, "  "),
        ("struct S  :tail", "struct S", STOP_COLON, "  "),
        ("struct S @  :tail", "struct S @", STOP_COLON, "  "),
        ("struct  {tail", "struct", STOP_LBRACE, "  "),
        ("struct S @  {tail", "struct S @", STOP_LBRACE, "  "),
        ("struct\r\n", "struct", STOP_COLON, "\r\n"),
        ("struct S\r\n", "struct S", STOP_COLON, "\r\n"),
    ] {
        let (green, exit, records) = typed_struct(source, 100, None, stops, None);
        assert_eq!(green.to_string(), text, "{source:?}");
        assert_eq!(records.len(), 1);
        let mut item = match exit {
            NormalizedExit::Complete(Err(Either::Left(item)), _) => item,
            NormalizedExit::Complete(Err(Either::Right(end)), _) => end.item,
            _ => panic!("protected item"),
        };
        assert_eq!(emit_pending_leading_text(&mut item), leading);
        if !source.contains('@') {
            assert_eq!(records[0].site.range, 100 + text.len()..100 + text.len());
        }
    }
    let fence = FenceBoundary {
        opener: FenceOpener {
            line: 0,
            marker: 0..3,
            marker_width: 3,
        },
        prefix_policy: FencePrefixPolicy::ActivePrefixQuote { depth: 2, base: 0 },
        close_column: 0,
    };
    for (source, text, range, kind) in [
        (
            "struct\r\n>> ```",
            "struct",
            108..108,
            RecoveryKind::Missing,
        ),
        (
            "struct @\r\n>> ```",
            "struct @",
            107..108,
            RecoveryKind::Error,
        ),
        (
            "struct S\r\n>> ```",
            "struct S",
            110..110,
            RecoveryKind::Missing,
        ),
        (
            "struct S @\r\n>> ```",
            "struct S @",
            109..110,
            RecoveryKind::Error,
        ),
    ] {
        let (green, exit, records) = typed_struct(source, 100, None, 0, Some(&fence));
        assert_eq!(green.to_string(), text);
        assert_eq!(records.len(), 1);
        assert_eq!(records[0].site.range, range);
        assert_eq!(records[0].kind, kind);
        assert!(
            matches!(exit, NormalizedExit::Complete(Err(Either::Left(ref item)), _) if item.payload_view().is_boundary())
        );
        let (again, _, frozen) = typed_struct(source, 100, Some(&records), 0, Some(&fence));
        assert_eq!(again, green);
        assert_eq!(frozen, records);
    }
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

fn assert_pending_word_with_leading(exit: Option<TailExit>, word: &str, leading: &str) {
    let mut item = match exit {
        Some(Err(Either::Left(item))) => item,
        Some(Err(Either::Right(end))) => end.item,
        _ => panic!("{word:?} must remain pending"),
    };
    assert_eq!(
        item.payload_view().token_kind(),
        Some(TokenKind::Identifier)
    );
    assert_eq!(item.payload_view().spelling(), Some(word));
    assert_eq!(emit_pending_leading_text(&mut item), leading);
}

#[test]
fn struct_c11_builds_exact_direct_topology_and_forms() {
    for (source, fields) in [
        ("struct Empty;", 0),
        ("my struct Point{x: F, y: Y}", 2),
        ("our struct Pair(F, G)", 2),
        ("pub struct Row:\n  x: F\n  y: Y", 2),
    ] {
        let (green, _) = run_statement(source);
        assert_eq!(green.to_string(), source, "{source:?}");
        let node = declaration(&green);
        assert_eq!(
            node.parent().map(|node| node.kind()),
            Some(SyntaxKind::Statement)
        );
        assert_eq!(count(&node, SyntaxKind::StructField), fields, "{source:?}");
        assert_eq!(
            count(&node, SyntaxKind::TypeExpression),
            fields,
            "{source:?}"
        );
        assert_eq!(count(&node, SyntaxKind::BindingHeader), 0, "{source:?}");
    }
}

#[test]
fn struct_c11_dispatch_is_exact_and_irrevocable() {
    for source in [
        "struct S;",
        "my struct S;",
        "our struct S;",
        "pub struct S;",
    ] {
        let (green, _) = run_statement(source);
        assert_eq!(green.to_string(), source);
        declaration(&green);
    }
    for source in ["structure", "structural", "my structure = value"] {
        let (green, _) = run_statement(source);
        assert!(
            !SyntaxNode::new_root(green)
                .descendants()
                .any(|node| node.kind() == SyntaxKind::StructDeclaration),
            "{source:?}"
        );
    }
    let (green, _) = run_statement("my struct = value");
    let root = SyntaxNode::new_root(green);
    assert!(
        root.descendants()
            .any(|node| node.kind() == SyntaxKind::StructDeclaration)
    );
    assert!(
        !root
            .descendants()
            .any(|node| node.kind() == SyntaxKind::BindingStatement)
    );
}

#[test]
fn struct_c11_keeps_dynamic_word_operator_names_raw() {
    let operators = OperatorTable::from_declarations([
        OperatorDeclaration::new("Dynamic", OperatorFixities::new().with_nullfix()),
        OperatorDeclaration::new("field", OperatorFixities::new().with_nullfix()),
    ])
    .expect("dynamic Struct-name operator table");
    let source = "struct Dynamic{field: T}";
    let (green, exit) = run_statement_with(source, &operators);
    assert_eq!(green.to_string(), source);
    assert!(matches!(exit, Some(Err(Either::Right(_)))));
    let node = declaration(&green);
    assert_eq!(count(&node, SyntaxKind::NullfixOperatorUse), 0);
    assert_eq!(count(&node, SyntaxKind::Error), 0);
    assert_eq!(count(&node, SyntaxKind::StructField), 1);
}

#[test]
fn struct_c11_named_boundary_splits_only_complete_next_fields() {
    for (source, fields, types, missing) in [
        ("struct S{x:F y:Y}", 2, 2, 1),
        ("struct S{x:F Y}", 1, 2, 0),
        ("struct S{x:Pair(F Y)}", 1, 3, 0),
        ("struct S(F Y)", 1, 2, 0),
    ] {
        let (green, _) = run_statement(source);
        assert_eq!(green.to_string(), source, "{source:?}");
        let node = declaration(&green);
        assert_eq!(count(&node, SyntaxKind::StructField), fields, "{source:?}");
        assert_eq!(
            count(&node, SyntaxKind::TypeExpression),
            types,
            "{source:?}"
        );
        assert_eq!(
            count(&node, SyntaxKind::Missing),
            missing,
            "{source:?}\n{node:#?}"
        );
    }
}

#[test]
fn struct_c11_gap_rules_keep_shallow_items_pending() {
    let (green, _) = run_statement("my\nstruct S;");
    assert!(
        !SyntaxNode::new_root(green)
            .descendants()
            .any(|node| node.kind() == SyntaxKind::StructDeclaration)
    );

    let (green, exit) = run_statement("struct\nName;");
    assert_eq!(green.to_string(), "struct");
    assert_eq!(count(&declaration(&green), SyntaxKind::Missing), 1);
    assert!(matches!(exit, Some(Err(Either::Left(_)))));

    for (source, fields, missing) in [
        ("struct S{x\n:y}", 2, 2),
        ("struct S{x\n  :y}", 2, 3),
        ("struct S{x:\nY}", 2, 2),
        ("struct S{x:\n  Y}", 1, 0),
    ] {
        let (green, _) = run_statement(source);
        assert_eq!(green.to_string(), source);
        let node = declaration(&green);
        assert_eq!(count(&node, SyntaxKind::StructField), fields, "{source:?}");
        assert_eq!(
            count(&node, SyntaxKind::Missing),
            missing,
            "{source:?}\n{node:#?}"
        );
    }
}

#[test]
fn struct_c11_header_and_body_recovery_stays_owner_local() {
    for (source, missing, errors) in [
        ("struct;", 1, 0),
        ("struct @ S;", 0, 1),
        ("struct S @ ;", 0, 1),
        ("struct S:", 1, 0),
    ] {
        let (green, _) = run_statement(source);
        assert_eq!(green.to_string(), source, "{source:?}");
        let node = declaration(&green);
        assert_eq!(count(&node, SyntaxKind::Missing), missing, "{source:?}");
        assert_eq!(count(&node, SyntaxKind::Error), errors, "{source:?}");
    }
}

#[test]
fn struct_c11_malformed_recovery_owns_trailing_eof_trivia() {
    for (source, error_parent, error_text) in [
        ("struct @ ", SyntaxKind::StructDeclaration, "@"),
        ("struct S @ ", SyntaxKind::StructDeclaration, "@"),
        ("struct S{x @ ", SyntaxKind::StructField, "@"),
        ("struct S{@ ", SyntaxKind::StructField, "@"),
    ] {
        let (green, _) = run_statement(source);
        assert_eq!(green.to_string(), source, "{source:?}");
        let root = SyntaxNode::new_root(green);
        let trailing = root
            .descendants_with_tokens()
            .filter_map(|element| element.into_token())
            .last()
            .expect("trailing EOF trivia token");
        assert_eq!(trailing.kind(), SyntaxKind::Whitespace, "{source:?}");
        assert_eq!(trailing.text(), " ", "{source:?}");
        if error_parent == SyntaxKind::StructDeclaration {
            // Header Error leaves terminal EOF leading to the pending Item.
            assert_eq!(trailing.parent().unwrap().kind(), SyntaxKind::Root);
        }
        let error = root
            .descendants()
            .find(|node| node.kind() == SyntaxKind::Error)
            .unwrap();
        assert_eq!(error.kind(), SyntaxKind::Error, "{source:?}");
        assert_eq!(error.to_string(), error_text, "{source:?}");
        assert_eq!(
            error.parent().map(|node| node.kind()),
            Some(error_parent),
            "{source:?}",
        );
    }
}

#[test]
fn struct_named_field_records_are_exact_and_frozen() {
    use crate::recovery_record::{
        DeclarationRole, DiagnosticId, ExpectationSources, ExpectedSyntax, GrammarRole,
        PunctuationEvidence, RecoveryKind, RecoverySiteKey, StructRole, SyntaxExpectation,
        UnexpectedCategory, UnexpectedSyntax,
    };
    use std::sync::Arc;

    for (source, slot, kind, range, expected) in [
        (
            "struct S{: T}",
            StructRole::FieldName,
            RecoveryKind::Missing,
            9..9,
            ExpectedSyntax::Identifier,
        ),
        (
            "struct S{x T}",
            StructRole::FieldColon,
            RecoveryKind::Missing,
            11..11,
            ExpectedSyntax::Punctuation(PunctuationEvidence::Colon),
        ),
        (
            "struct S{@ : T}",
            StructRole::FieldName,
            RecoveryKind::Error,
            9..10,
            ExpectedSyntax::Identifier,
        ),
        (
            "struct S{x @ : T}",
            StructRole::FieldColon,
            RecoveryKind::Error,
            11..12,
            ExpectedSyntax::Punctuation(PunctuationEvidence::Colon),
        ),
    ] {
        let (green, _, records) = typed_struct(source, 100, None, 0, None);
        assert_eq!(green.to_string(), source, "{source:?}");
        let range = range.start + 100..range.end + 100;
        let role = GrammarRole::Declaration(DeclarationRole::Struct(slot));
        assert_eq!(
            records,
            [CommittedRecoveryRecord {
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
                expectations: Arc::from([SyntaxExpectation {
                    role,
                    expected,
                    range: range.clone(),
                    sources: ExpectationSources::COMMITTED_RECOVERY_RULE,
                }]),
                primary_expectation: 0,
            }],
            "{source:?}",
        );
        let mut seeded = records.clone();
        seeded[0].id = DiagnosticId(71);
        let (again, _, frozen) = typed_struct(source, 100, Some(&seeded), 0, None);
        assert_eq!(again, green, "{source:?}");
        assert_eq!(frozen, seeded, "{source:?}");
    }

    let (green, _, records) = typed_struct("struct S{@ x: T}", 100, None, 0, None);
    assert_eq!(green.to_string(), "struct S{@ x: T}");
    let field = GrammarRole::Declaration(DeclarationRole::Struct(StructRole::Field));
    let separator = GrammarRole::Declaration(DeclarationRole::Struct(StructRole::FieldSeparator));
    assert_eq!(
        records,
        [
            CommittedRecoveryRecord {
                id: DiagnosticId(0),
                site: RecoverySiteKey {
                    role: field,
                    range: 109..110
                },
                kind: RecoveryKind::Error,
                unexpected: Arc::from([UnexpectedSyntax::Token {
                    range: 109..110,
                    category: UnexpectedCategory::OtherCharacter,
                }]),
                expectations: Arc::from([SyntaxExpectation {
                    role: field,
                    expected: ExpectedSyntax::Identifier,
                    range: 109..110,
                    sources: ExpectationSources::COMMITTED_RECOVERY_RULE,
                }]),
                primary_expectation: 0,
            },
            CommittedRecoveryRecord {
                id: DiagnosticId(1),
                site: RecoverySiteKey {
                    role: separator,
                    range: 111..111
                },
                kind: RecoveryKind::Missing,
                unexpected: Arc::from([]),
                expectations: Arc::from([SyntaxExpectation {
                    role: separator,
                    expected: ExpectedSyntax::DelimitedSequenceSeparator,
                    range: 111..111,
                    sources: ExpectationSources::COMMITTED_RECOVERY_RULE,
                }]),
                primary_expectation: 0,
            },
        ]
    );
}

#[test]
fn struct_named_field_runs_keep_per_item_facts_and_active_stops_pending() {
    use crate::{
        lexical::stops::STOP_COLON,
        recovery_record::{
            DeclarationRole, GrammarRole, StructRole, UnexpectedCategory, UnexpectedSyntax,
        },
    };

    let (green, _, records) = typed_struct("struct S{@ # : T}", 100, None, 0, None);
    assert_eq!(green.to_string(), "struct S{@ # : T}");
    assert_eq!(records.len(), 1);
    assert_eq!(
        records[0].site.role,
        GrammarRole::Declaration(DeclarationRole::Struct(StructRole::FieldName))
    );
    assert_eq!(records[0].site.range, 109..112);
    assert_eq!(
        records[0].unexpected,
        [
            UnexpectedSyntax::Token {
                range: 109..110,
                category: UnexpectedCategory::OtherCharacter,
            },
            UnexpectedSyntax::Token {
                range: 110..112,
                category: UnexpectedCategory::OtherCharacter,
            }
        ]
        .into()
    );

    for (source, stops, text, slot, pending) in [
        (
            "struct S{x : T}",
            STOP_COLON,
            "struct S{x ",
            StructRole::FieldColon,
            TokenKind::Colon,
        ),
        (
            "struct S{x @ : T}",
            STOP_COLON,
            "struct S{x @",
            StructRole::FieldColon,
            TokenKind::Colon,
        ),
    ] {
        let (green, exit, records) = typed_struct(source, 100, None, stops, None);
        assert_eq!(green.to_string(), text, "{source:?}");
        assert_eq!(records.len(), 2, "{source:?}");
        assert_eq!(
            records[0].site.role,
            GrammarRole::Declaration(DeclarationRole::Struct(slot)),
            "{source:?}",
        );
        assert_eq!(
            records[1].site.role,
            GrammarRole::ClosingDelimiter {
                owner: crate::recovery_record::ConstructRole::StructNamedFields,
                delimiter: crate::recovery_record::Delimiter::Brace,
            },
            "{source:?}",
        );
        let NormalizedExit::Complete(Err(Either::Left(item)), LineEntry::InLine) = exit else {
            panic!("active field boundary must stay pending: {source:?}")
        };
        assert_eq!(
            item.payload_view().token_kind(),
            Some(pending),
            "{source:?}"
        );
    }
}

#[test]
fn struct_field_lists_publish_their_own_missing_and_mismatched_close() {
    use crate::recovery_record::{
        ConstructRole, Delimiter, ExpectedSyntax, GrammarRole, PunctuationEvidence, RecoveryKind,
    };

    for (source, owner, delimiter, kind, range) in [
        (
            "struct S{",
            ConstructRole::StructNamedFields,
            Delimiter::Brace,
            RecoveryKind::Missing,
            109..109,
        ),
        (
            "struct S(",
            ConstructRole::StructTupleFields,
            Delimiter::Parenthesis,
            RecoveryKind::Missing,
            109..109,
        ),
    ] {
        let (green, _, records) = typed_struct(source, 100, None, 0, None);
        assert_eq!(green.to_string(), source, "{source:?}");
        let role = GrammarRole::ClosingDelimiter { owner, delimiter };
        assert_eq!(records.len(), 1, "{source:?}");
        assert_eq!(
            records[0].site,
            crate::recovery_record::RecoverySiteKey {
                role,
                range: range.clone()
            }
        );
        assert_eq!(records[0].kind, kind, "{source:?}");
        assert_eq!(
            records[0].expectations[0].expected,
            ExpectedSyntax::Punctuation(PunctuationEvidence::Close(delimiter))
        );
        assert_eq!(
            records[0].unexpected.len(),
            usize::from(kind == RecoveryKind::Error)
        );
    }

    let (green, _, records) = typed_struct("struct S{)", 100, None, 0, None);
    assert_eq!(green.to_string(), "struct S{)");
    let role = GrammarRole::ClosingDelimiter {
        owner: ConstructRole::StructNamedFields,
        delimiter: Delimiter::Brace,
    };
    assert_eq!(records.len(), 2);
    assert_eq!(records[0].site.role, role);
    assert_eq!(records[0].kind, RecoveryKind::Error);
    assert_eq!(records[0].site.range, 109..110);
    assert_eq!(records[1].site.role, role);
    assert_eq!(records[1].kind, RecoveryKind::Missing);
    assert_eq!(records[1].site.range, 110..110);
}

#[test]
fn struct_c11_gstruct_and_body_handoff_are_lossless() {
    for source in ["struct\n  Deep;", "struct Adjacent{}"] {
        let (green, _) = run_statement(source);
        assert_eq!(green.to_string(), source, "{source:?}");
        declaration(&green);
    }
    let (green, _) = run_statement("struct S Foo");
    let node = declaration(&green);
    assert_eq!(green.to_string(), "struct S ");
    assert_eq!(count(&node, SyntaxKind::StructField), 0);
    assert_eq!(count(&node, SyntaxKind::Missing), 1);

    let (green, exit) = run_statement("struct S 1");
    let node = declaration(&green);
    assert_eq!(green.to_string(), "struct S ");
    assert_eq!(count(&node, SyntaxKind::Missing), 1);
    assert_eq!(count(&node, SyntaxKind::Error), 0);
    assert!(matches!(exit, Some(Err(Either::Left(_)))));

    let (green, exit) = run_statement("struct S\nnext");
    assert_eq!(green.to_string(), "struct S");
    let Err(Either::Left(mut item)) = exit.expect("statement exit") else {
        panic!("pending item")
    };
    assert_eq!(emit_pending_leading_text(&mut item), "\n");

    let (green, exit) = run_statement("struct S:\nnext");
    assert_eq!(count(&declaration(&green), SyntaxKind::StructField), 1);
    assert!(matches!(exit, Some(Err(Either::Left(_)))));
}

#[test]
fn struct_c11_body_colon_does_not_capture_polymorphic_variant_type() {
    let (green, exit) = run_statement("struct S :{A}");
    let node = declaration(&green);
    assert_eq!(green.to_string(), "struct S ");
    assert_eq!(count(&node, SyntaxKind::Missing), 1);
    assert_eq!(count(&node, SyntaxKind::Error), 0);
    let Some(Err(Either::Left(item))) = exit else {
        panic!("polymorphic variant type must remain pending")
    };
    assert_eq!(
        item.payload_view().token_kind(),
        Some(TokenKind::PolymorphicVariantColon)
    );
    assert_eq!(item.payload_view().spelling(), Some(":"));

    let source = "struct S:\n  x: T";
    let (green, _) = run_statement(source);
    assert_eq!(green.to_string(), source);
    let node = declaration(&green);
    assert_eq!(count(&node, SyntaxKind::StructField), 1);
    assert_eq!(count(&node, SyntaxKind::Missing), 0);
}

#[test]
fn struct_c11_tuple_uses_the_complete_type_vocabulary() {
    let source = "struct S(for 'a: T, '[E], :{A}, [R])";
    let (green, _) = run_statement(source);
    assert_eq!(green.to_string(), source);
    let node = declaration(&green);
    assert_eq!(count(&node, SyntaxKind::StructField), 4);
    for kind in [
        SyntaxKind::ForallType,
        SyntaxKind::EffectRowType,
        SyntaxKind::PolymorphicVariantType,
        SyntaxKind::BracketRow,
    ] {
        assert_eq!(count(&node, kind), 1, "{kind:?}");
    }

    let source = "struct S(A; for 'a: T)";
    let (green, _) = run_statement(source);
    assert_eq!(green.to_string(), source);
    let node = declaration(&green);
    assert_eq!(count(&node, SyntaxKind::StructField), 2);
    assert_eq!(count(&node, SyntaxKind::ForallType), 1);

    let source = "struct S(,A,,)";
    let (green, _) = run_statement(source);
    assert_eq!(green.to_string(), source);
    let node = declaration(&green);
    let fields = node
        .children()
        .filter(|child| child.kind() == SyntaxKind::StructField)
        .collect::<Vec<_>>();
    assert_eq!(fields.len(), 3);
    assert!(fields.iter().all(|field| {
        field
            .children()
            .all(|child| child.kind() == SyntaxKind::TypeExpression)
            && field
                .children()
                .any(|child| child.kind() == SyntaxKind::TypeExpression)
    }));
}

#[test]
fn struct_c11_trivia_stays_with_the_struct_sequence_and_named_gap() {
    let source = "struct S(\n  A, /*post*/\n  B\n)";
    let (green, _) = run_statement(source);
    assert_eq!(green.to_string(), source);
    let node = declaration(&green);
    let tuple_fields = node
        .children()
        .filter(|child| child.kind() == SyntaxKind::StructField)
        .collect::<Vec<_>>();
    assert_eq!(tuple_fields.len(), 2);
    assert!(tuple_fields.iter().all(|field| {
        field
            .children()
            .map(|child| child.kind())
            .collect::<Vec<_>>()
            == [SyntaxKind::TypeExpression]
            && field
                .children_with_tokens()
                .all(|element| element.as_token().is_none())
    }));
    assert!(
        node.descendants_with_tokens()
            .filter_map(|element| element.into_token())
            .filter(|token| matches!(
                token.kind(),
                SyntaxKind::Whitespace | SyntaxKind::Newline | SyntaxKind::BlockComment
            ))
            .all(|token| token.parent().as_ref() == Some(&node))
    );

    let source = "struct S{\n  x :  F,\n  y:Y\n}";
    let (green, _) = run_statement(source);
    assert_eq!(green.to_string(), source);
    let node = declaration(&green);
    let first = node
        .children()
        .find(|child| child.kind() == SyntaxKind::StructField)
        .expect("named field");
    let ty = first
        .children()
        .find(|child| child.kind() == SyntaxKind::TypeExpression)
        .expect("field type");
    assert_eq!(ty.text().to_string(), "F");
    assert_eq!(first.text().to_string(), "x :  F");
}

#[test]
fn struct_c11_recovers_owned_fields_and_typed_closes() {
    for source in [
        "struct S{x F, y: Y}",
        "struct S{: F}",
        "struct S{x: , y:Y}",
        "struct S{x:F; y:Y}",
        "struct S{x:F; :Y}",
        "struct S(F; G)",
        "struct S{x:F] y:Y}",
        "struct S(F} G)",
        "struct S{x:F",
        "struct S(F",
    ] {
        let (green, _) = run_statement(source);
        assert_eq!(green.to_string(), source, "{source:?}");
        declaration(&green);
    }
}

#[test]
fn struct_c11_reaches_nested_canonical_consumers_but_not_inline_expr_slots() {
    for source in [
        "{struct S;}",
        "f:\n  struct S;",
        "if c:\n  struct S;",
        "case x:\n  p ->\n    struct S;",
        "catch x:\n  p ->\n    struct S;",
        "value with: struct S;",
        "value with:\n  struct S;",
        "mod M {struct S;}",
        "mod M:\n  struct S;",
        "mod M: struct S;",
        "my body =\n  struct S;",
    ] {
        let (green, _) = run_statement(source);
        assert_eq!(green.to_string(), source, "{source:?}");
        declaration(&green);
    }
    for source in [
        "f: struct S;",
        "if c: struct S;",
        "case x: p -> struct S;",
        "catch x: p -> struct S;",
        "my x = struct S;",
        "f struct S;",
    ] {
        let (green, _) = run(source);
        assert!(source.starts_with(&green.to_string()), "{source:?}");
        assert!(
            !SyntaxNode::new_root(green)
                .descendants()
                .any(|node| node.kind() == SyntaxKind::StructDeclaration),
            "{source:?}"
        );
    }
}

#[test]
fn struct_companion_header_orders_derives_before_the_companion() {
    for (source, missing, errors) in [
        ("struct S with {}", 0, 0),
        ("struct S derives Eq with {}", 0, 0),
        ("struct S derives with {}", 1, 0),
        ("struct S derives @ with {}", 0, 1),
    ] {
        let (green, _) = run_statement(source);
        assert_eq!(green.to_string(), source, "{source:?}");
        let node = declaration(&green);
        assert_eq!(
            count(&node, SyntaxKind::DeclarationCompanion),
            1,
            "{source:?}"
        );
        assert_eq!(token_count(&node, SyntaxKind::WithKw), 1, "{source:?}");
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
        let owned = node
            .children()
            .filter(|child| {
                matches!(
                    child.kind(),
                    SyntaxKind::DerivesClause | SyntaxKind::DeclarationCompanion
                )
            })
            .map(|child| child.kind())
            .collect::<Vec<_>>();
        assert_eq!(
            owned.last(),
            Some(&SyntaxKind::DeclarationCompanion),
            "{source:?}: {owned:?}",
        );
    }
}

#[test]
fn struct_companion_trailing_follows_the_actual_matching_close() {
    for source in [
        "struct S{} derives Eq with {}",
        "struct S(A) derives Eq with {}",
        "struct S{x F} with {}",
        "struct S{x:F; y:Y} with {}",
        "struct S{x:F] y:Y} with {}",
        "struct S(@) with {}",
        "struct S(A; B) with {}",
    ] {
        let (green, _) = run_statement(source);
        assert_eq!(green.to_string(), source, "{source:?}");
        let node = declaration(&green);
        assert_eq!(
            count(&node, SyntaxKind::DeclarationCompanion),
            1,
            "{source:?}"
        );
    }

    for source in [
        "struct S{x:T with {}",
        "struct S{x:T] with ()",
        "struct S(A] with {}",
    ] {
        let (green, _) = run_statement(source);
        assert_eq!(green.to_string(), source, "{source:?}");
        let node = declaration(&green);
        assert_eq!(
            count(&node, SyntaxKind::DeclarationCompanion),
            0,
            "{source:?}"
        );
    }
}

#[test]
fn struct_header_derives_hands_body_starters_back_by_role_phase() {
    for (source, fields) in [
        ("struct S derives {}", 0),
        ("struct S derives :\n  x:T", 1),
        ("struct S derives ;", 0),
        ("struct S derives Eq{}", 0),
        ("struct S derives Eq(A)", 1),
        ("struct S derives Eq:\n  x:T", 1),
        ("struct S derives Eq;", 0),
    ] {
        let (green, _) = run_statement(source);
        assert_eq!(green.to_string(), source, "{source:?}");
        let node = declaration(&green);
        assert_eq!(count(&node, SyntaxKind::DerivesClause), 1, "{source:?}");
        assert_eq!(count(&node, SyntaxKind::StructField), fields, "{source:?}");
        assert_eq!(count(&node, SyntaxKind::DeclarationCompanion), 0);
    }

    for source in [
        "struct S derives (Eq) with {}",
        "struct S derives (Eq(A)) with {}",
        "struct S derives (Eq {x:T}) with {}",
    ] {
        let (green, _) = run_statement(source);
        assert_eq!(green.to_string(), source, "{source:?}");
        let node = declaration(&green);
        assert_eq!(count(&node, SyntaxKind::DerivesClause), 1, "{source:?}");
        assert_eq!(count(&node, SyntaxKind::DeclarationCompanion), 1);
        assert_eq!(count(&node, SyntaxKind::StructField), 0, "{source:?}");
    }

    let source = "struct S derives , with {}";
    let (green, _) = run_statement(source);
    assert_eq!(green.to_string(), source);
    let node = declaration(&green);
    assert_eq!(count(&node, SyntaxKind::DerivesClause), 1);
    assert_eq!(count(&node, SyntaxKind::DeclarationCompanion), 1);
    assert_eq!(count(&node, SyntaxKind::Missing), 2);
}

#[test]
fn struct_companion_rejects_nontrailing_body_forms_and_incomplete_name() {
    for (source, leading) in [
        ("struct S; with {}", " "),
        ("struct S:\n  x:T\nwith {}", "\n"),
        ("struct ; with {}", " "),
    ] {
        let (green, exit) = run_statement(source);
        assert_eq!(
            count(&declaration(&green), SyntaxKind::DeclarationCompanion),
            0,
            "{source:?}"
        );
        assert_pending_word_with_leading(exit, "with", leading);
    }

    let source = "struct S{x:T\nwith {}";
    let (green, _) = run_statement(source);
    assert_eq!(green.to_string(), source);
    assert_eq!(
        count(&declaration(&green), SyntaxKind::DeclarationCompanion),
        0
    );
}

#[test]
fn struct_companion_suspends_with_inside_nested_derives_types() {
    let source = "struct S derives (A with B) with {}";
    let (green, _) = run_statement(source);
    assert_eq!(green.to_string(), source);
    let node = declaration(&green);
    assert_eq!(count(&node, SyntaxKind::DeclarationCompanion), 1);
    assert_eq!(token_count(&node, SyntaxKind::WithKw), 1);
    assert!(
        node.descendants_with_tokens()
            .filter_map(|element| element.into_token())
            .any(|token| token.kind() == SyntaxKind::Identifier && token.text() == "with")
    );
}

#[test]
fn struct_companion_gap_and_contextual_word_judges_are_exact() {
    for source in ["struct S\n  with {}", "struct S\r\n  with {}"] {
        let (green, _) = run_statement(source);
        assert_eq!(green.to_string(), source, "{source:?}");
        assert_eq!(
            count(&declaration(&green), SyntaxKind::DeclarationCompanion),
            1
        );
    }
    for (source, leading) in [
        ("struct S\nwith {}", "\n"),
        ("struct S{}\r\nwith {}", "\r\n"),
    ] {
        let (green, exit) = run_statement(source);
        assert_eq!(
            count(&declaration(&green), SyntaxKind::DeclarationCompanion),
            0
        );
        assert_pending_word_with_leading(exit, "with", leading);
    }

    let operators = OperatorTable::from_declarations([OperatorDeclaration::new(
        "with",
        OperatorFixities::new().with_nullfix(),
    )])
    .expect("dynamic with operator table");
    let (green, exit) = run_statement_with("struct S{} with {}", &operators);
    assert_eq!(
        count(&declaration(&green), SyntaxKind::DeclarationCompanion),
        0
    );
    assert!(matches!(
        exit,
        Some(Err(Either::Left(_))) | Some(Err(Either::Right(_)))
    ));

    let (green, exit) = run_statement_with_stops(
        "struct S with {}",
        &OperatorTable::empty(),
        crate::lexical::stops::STOP_WITH,
    );
    assert_eq!(
        count(&declaration(&green), SyntaxKind::DeclarationCompanion),
        0
    );
    assert_pending_word_with_leading(exit, "with", " ");

    for source in ["struct S withx {}", "struct S within {}"] {
        let (green, _) = run_statement(source);
        assert_eq!(
            count(&declaration(&green), SyntaxKind::DeclarationCompanion),
            0,
            "{source:?}"
        );
    }
}

#[test]
fn struct_companion_rejected_incomplete_lists_keep_the_exact_fence_handoff() {
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
    let origin = 8200;
    for accepted in [
        "> > struct S{x:T with {}",
        "> > struct S{x:T] with {}",
        "> > struct S(A with B",
        "> > struct S(A] with B",
    ] {
        let source = format!("{accepted}\r\n> > ```\r\nouter");
        let (green, exit, remainder) =
            run_statement_normalized(&source, origin, LineEntry::PhysicalStart, Some(&fence));
        let NormalizedExit::Complete(Err(Either::Left(boundary)), LineEntry::PhysicalStart) = exit
        else {
            panic!("the incomplete Struct body must return its exact fence boundary")
        };

        assert_eq!(green.to_string(), accepted, "{accepted:?}");
        assert_eq!(remainder, "> > ```\r\nouter", "{accepted:?}");
        let node = declaration(&green);
        assert_eq!(
            count(&node, SyntaxKind::DeclarationCompanion),
            0,
            "{accepted:?}\n{node:#?}",
        );
        assert!(boundary.payload_view().is_boundary(), "{accepted:?}");
        let (leading, pending) = emit_terminal_leading_text(boundary);
        assert_eq!(leading, "\r\n", "{accepted:?}");
        assert_eq!(
            pending.coordinate(),
            origin + accepted.len() + 2,
            "{accepted:?}",
        );
        assert!(matches!(
            pending.into_kind(),
            Boundary::BorrowedClose(BorrowedTarget::YumarkFence(_))
        ));
    }
}

#[test]
fn struct_actual_close_returns_the_exact_normalized_successor() {
    let origin = 8300;
    for declaration_text in ["struct S{x:T}", "struct S(T)"] {
        let source = format!("{declaration_text}  next tail");
        let (green, exit, remainder) =
            run_statement_normalized(&source, origin, LineEntry::InLine, None);
        let NormalizedExit::Complete(Err(Either::Left(mut successor)), LineEntry::InLine) = exit
        else {
            panic!("the closed Struct must return its exact successor")
        };

        assert_eq!(green.to_string(), declaration_text, "{declaration_text:?}");
        assert_eq!(remainder, " tail", "{declaration_text:?}");
        assert_eq!(
            successor.payload_view().token_kind(),
            Some(TokenKind::Identifier),
            "{declaration_text:?}",
        );
        assert_eq!(
            successor.payload_view().spelling(),
            Some("next"),
            "{declaration_text:?}",
        );
        assert_eq!(
            origin + source.len() - remainder.len() - "next".len(),
            origin + declaration_text.len() + 2,
            "{declaration_text:?}",
        );
        assert_eq!(
            emit_pending_leading_text(&mut successor),
            "  ",
            "{declaration_text:?}",
        );
        assert_eq!(
            count(&declaration(&green), SyntaxKind::DeclarationCompanion),
            0,
            "{declaration_text:?}",
        );
    }
}

#[test]
fn struct_accepted_companion_returns_the_exact_outer_remainder() {
    let origin = 8400;
    for declaration_text in ["struct S{} with {}", "struct S(T) with {}"] {
        let source = format!("{declaration_text} outer tail");
        let (green, exit, remainder) =
            run_statement_normalized(&source, origin, LineEntry::InLine, None);
        assert!(matches!(
            exit,
            NormalizedExit::Complete(Ok(()), LineEntry::InLine)
        ));

        assert_eq!(green.to_string(), declaration_text, "{declaration_text:?}");
        assert_eq!(remainder, " outer tail", "{declaration_text:?}");
        let node = declaration(&green);
        assert_eq!(count(&node, SyntaxKind::DeclarationCompanion), 1);
        assert_eq!(token_count(&node, SyntaxKind::WithKw), 1);
    }
}

#[test]
fn struct_companion_streams_crlf_to_the_same_fence_boundary() {
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
    let origin = 8100;
    let accepted = "> > struct S{} derives Eq with: our x = y";
    let source = format!("{accepted}\r\n> > ```\r\nouter");
    let (green, exit, remainder) =
        run_statement_normalized(&source, origin, LineEntry::PhysicalStart, Some(&fence));
    let NormalizedExit::Complete(Err(Either::Left(boundary)), LineEntry::PhysicalStart) = exit
    else {
        panic!("the Struct companion must return the exact fence boundary")
    };
    assert!(boundary.payload_view().is_boundary());
    assert_eq!(green.to_string(), accepted);
    assert_eq!(remainder, "> > ```\r\nouter");
    let node = declaration(&green);
    assert_eq!(count(&node, SyntaxKind::DeclarationCompanion), 1);
    assert_eq!(token_count(&node, SyntaxKind::WithKw), 1);
    let (leading, pending) = emit_terminal_leading_text(boundary);
    assert_eq!(leading, "\r\n");
    assert_eq!(pending.coordinate(), origin + accepted.len() + 2);
}
