use super::*;
use crate::rewrite::yumark::{FenceOpener, FencePrefixPolicy};

fn typed_mod<'s>(
    source: &'s str,
    frozen: Option<&[CommittedRecoveryRecord]>,
    stops: Stops,
) -> (
    GreenNode,
    NormalizedExit,
    Vec<CommittedRecoveryRecord>,
    &'s str,
) {
    typed_mod_fenced(source, frozen, stops, None)
}

fn typed_mod_fenced<'s>(
    source: &'s str,
    frozen: Option<&[CommittedRecoveryRecord]>,
    stops: Stops,
    fence: Option<&FenceBoundary>,
) -> (
    GreenNode,
    NormalizedExit,
    Vec<CommittedRecoveryRecord>,
    &'s str,
) {
    let operators = OperatorTable::empty();
    let mut input = source;
    let mut recover = Recover::new(&operators);
    let mut builder = frozen.map_or_else(GreenNodeBuilder::new, GreenNodeBuilder::reconcile);
    builder.start_node(SyntaxKind::Root.into());
    let exit = statement_normalized(
        In::new(&mut input, &mut recover, &mut builder),
        0,
        stops,
        100,
        LineEntry::InLine,
        fence,
        Some(crate::rewrite::ambient_claim::AmbientClaimView::root_statement(0)).into(),
        Some(crate::rewrite::sequence::SequenceOwner::RootStatement),
    );
    builder.finish_node();
    let (green, records) = builder.finish_with_recoveries();
    (green, exit, records, input)
}

#[test]
fn mod_typed_protected_items_keep_leading_and_fence_coordinates() {
    for (source, owned, leading) in [
        ("mod  else", "mod", "  "),
        ("mod A  else", "mod A", "  "),
        ("mod A:  else", "mod A:", "  "),
        ("mod A:\r\nnext", "mod A:", "\r\n"),
        ("mod A: @  else", "mod A: @", "  "),
    ] {
        let (green, exit, records, remainder) = typed_mod(source, None, STOP_ELSE);
        assert_eq!(green.to_string(), owned);
        let NormalizedExit::Complete(Err(Either::Left(mut item)), line) = exit else {
            panic!("protected Item")
        };
        assert_eq!(emit_pending_leading_text(&mut item), leading);
        assert_eq!(remainder, "");
        assert_eq!(token_kind(&item), Some(TokenKind::Identifier));
        assert_eq!(
            item.payload_view().spelling(),
            Some(if source.ends_with("next") {
                "next"
            } else {
                "else"
            })
        );
        assert_eq!(line, LineEntry::InLine);
        assert_eq!(records.len(), 1);
        let (again, exit, frozen, remainder) = typed_mod(source, Some(&records), STOP_ELSE);
        assert_eq!(again, green);
        assert_eq!(frozen, records);
        assert_eq!(remainder, "");
        let NormalizedExit::Complete(Err(Either::Left(mut item)), line) = exit else {
            panic!("frozen protected Item")
        };
        assert_eq!(emit_pending_leading_text(&mut item), leading);
        assert_eq!(token_kind(&item), Some(TokenKind::Identifier));
        assert_eq!(
            item.payload_view().spelling(),
            Some(if source.ends_with("next") {
                "next"
            } else {
                "else"
            })
        );
        assert_eq!(line, LineEntry::InLine);
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
    for (source, owned, range) in [
        ("mod\r\n>> ```", "mod", 105..105),
        ("mod A\r\n>> ```", "mod A", 107..107),
        ("mod A:\r\n>> ```", "mod A:", 108..108),
        ("mod A: @\r\n>> ```", "mod A: @", 107..108),
    ] {
        let (green, exit, records, remainder) = typed_mod_fenced(source, None, 0, Some(&fence));
        assert_eq!(green.to_string(), owned);
        assert_eq!(records.len(), 1);
        assert_eq!(records[0].site.range, range);
        let NormalizedExit::Complete(Err(Either::Left(item)), line) = exit else {
            panic!("protected fence")
        };
        let (leading, boundary) = emit_terminal_leading_text(item);
        assert_eq!(leading, "\r\n");
        assert_eq!(boundary.coordinate(), 100 + owned.len() + 2);
        assert!(matches!(
            boundary.kind(),
            super::super::item::Boundary::BorrowedClose(
                super::super::item::BorrowedTarget::YumarkFence(_)
            )
        ));
        assert_eq!(line, LineEntry::PhysicalStart);
        assert_eq!(remainder, ">> ```");
        let (again, exit, frozen, remainder) =
            typed_mod_fenced(source, Some(&records), 0, Some(&fence));
        assert_eq!(again, green);
        assert_eq!(frozen, records);
        let NormalizedExit::Complete(Err(Either::Left(item)), frozen_line) = exit else {
            panic!("frozen protected fence")
        };
        let (frozen_leading, frozen_boundary) = emit_terminal_leading_text(item);
        assert_eq!(frozen_leading, leading);
        assert_eq!(frozen_boundary, boundary);
        assert_eq!(frozen_line, line);
        assert_eq!(remainder, ">> ```");
    }
}

#[test]
fn mod_typed_slots_preserve_shifted_frozen_records_and_leading() {
    use crate::session::{
        DeclarationRole, Delimiter, DiagnosticId, ExpectationSources, ExpectedSyntax, GrammarRole,
        ModRole, PunctuationEvidence, RecoveryKind, RecoverySiteKey, SyntaxExpectation,
        UnexpectedCategory, UnexpectedSyntax,
    };
    use std::sync::Arc;
    for (source, slot, kind, range, text, colon_only) in [
        (
            "mod  ",
            ModRole::Name,
            RecoveryKind::Missing,
            5..5,
            "mod  ",
            false,
        ),
        (
            "mod test  ",
            ModRole::TestName,
            RecoveryKind::Missing,
            10..10,
            "mod test  ",
            false,
        ),
        (
            "mod ;",
            ModRole::Name,
            RecoveryKind::Missing,
            4..4,
            "mod ;",
            false,
        ),
        (
            "mod @ # 名;",
            ModRole::Name,
            RecoveryKind::Error,
            4..7,
            "mod @ # 名;",
            false,
        ),
        (
            "mod test @ test;",
            ModRole::TestName,
            RecoveryKind::Error,
            9..10,
            "mod test @ test;",
            false,
        ),
        (
            "mod @  ",
            ModRole::Name,
            RecoveryKind::Error,
            4..5,
            "mod @",
            false,
        ),
        (
            "mod 名  ",
            ModRole::BodyIntroducer,
            RecoveryKind::Missing,
            9..9,
            "mod 名  ",
            false,
        ),
        (
            "mod A x",
            ModRole::BodyIntroducer,
            RecoveryKind::Missing,
            6..6,
            "mod A x",
            true,
        ),
        (
            "mod A @ # : x",
            ModRole::BodyIntroducer,
            RecoveryKind::Error,
            6..9,
            "mod A @ # : x",
            false,
        ),
        (
            "mod A @  ",
            ModRole::BodyIntroducer,
            RecoveryKind::Error,
            6..7,
            "mod A @",
            false,
        ),
        (
            "mod A:  ",
            ModRole::Body,
            RecoveryKind::Missing,
            6..6,
            "mod A:",
            false,
        ),
        (
            "mod A:\r\nnext",
            ModRole::Body,
            RecoveryKind::Missing,
            6..6,
            "mod A:",
            false,
        ),
        (
            "mod A: @ # x;",
            ModRole::Body,
            RecoveryKind::Error,
            7..10,
            "mod A: @ # x;",
            false,
        ),
        (
            "mod A: @  ",
            ModRole::Body,
            RecoveryKind::Error,
            7..8,
            "mod A: @",
            false,
        ),
    ] {
        let (green, _, records, _) = typed_mod(source, None, 0);
        assert_eq!(green.to_string(), text, "{source:?}");
        let role = GrammarRole::Declaration(DeclarationRole::Mod(slot));
        let range = 100 + range.start..100 + range.end;
        let expected = match slot {
            ModRole::Name | ModRole::TestName => vec![ExpectedSyntax::Identifier],
            ModRole::Body => vec![ExpectedSyntax::Statement],
            _ if colon_only => vec![ExpectedSyntax::Punctuation(PunctuationEvidence::Colon)],
            _ => vec![
                ExpectedSyntax::Punctuation(PunctuationEvidence::Semicolon),
                ExpectedSyntax::Punctuation(PunctuationEvidence::Open(Delimiter::Brace)),
                ExpectedSyntax::Punctuation(PunctuationEvidence::Colon),
            ],
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
        let (again, _, frozen, _) = typed_mod(source, Some(&seeded), 0);
        assert_eq!(again, green);
        assert_eq!(frozen, seeded);
    }
}

#[test]
fn mod_test_name_test_is_an_identifier_on_admission_and_retry() {
    for source in ["mod test test;", "mod test @ test;"] {
        let (green, _, _, _) = typed_mod(source, None, 0);
        let declaration = mod_declaration(&green);
        assert_eq!(descendants(&declaration, SyntaxKind::TestModuleMarker), 1);
        assert_eq!(
            declaration
                .children_with_tokens()
                .filter_map(|element| element.into_token())
                .filter(|token| token.kind() == SyntaxKind::Identifier)
                .map(|token| token.text().to_string())
                .collect::<Vec<_>>(),
            ["test"]
        );
    }
}

#[test]
fn mod_typed_recovery_keeps_nested_binding_body_owner() {
    use crate::session::{BindingRole, DeclarationRole, GrammarRole};
    for source in ["mod A: my x =", "mod A {my x =}", "mod A:\n  my x ="] {
        let (_, _, records, _) = typed_mod(source, None, 0);
        assert_eq!(records.len(), 1, "{source:?}");
        assert_eq!(
            records[0].site.role,
            GrammarRole::Declaration(DeclarationRole::Binding(BindingRole::Body))
        );
    }
}

fn mod_declaration(green: &GreenNode) -> SyntaxNode {
    SyntaxNode::new_root(green.clone())
        .descendants()
        .find(|node| node.kind() == SyntaxKind::ModDeclaration)
        .expect("ModDeclaration")
}

fn descendants(node: &SyntaxNode, kind: SyntaxKind) -> usize {
    node.descendants()
        .filter(|descendant| descendant.kind() == kind)
        .count()
}

#[test]
fn mod_c10_builds_named_and_test_identity_topology() {
    for (source, visibility, marker, direct_names) in [
        ("mod Foo;", None, false, vec!["Foo"]),
        (
            "my mod error;",
            Some(SyntaxKind::MyKw),
            false,
            vec!["error"],
        ),
        ("our mod test;", Some(SyntaxKind::OurKw), true, vec![]),
        (
            "pub mod test parser;",
            Some(SyntaxKind::PubKw),
            true,
            vec!["parser"],
        ),
        ("mod testable;", None, false, vec!["testable"]),
    ] {
        let (green, exit) = run_statement(source);
        assert_eq!(green.to_string(), source, "{source:?}");
        assert!(matches!(exit, Some(Err(Either::Right(_)))), "{source:?}");
        let declaration = mod_declaration(&green);
        assert_eq!(
            declaration.parent().map(|node| node.kind()),
            Some(SyntaxKind::Statement)
        );
        assert_eq!(
            descendants(&declaration, SyntaxKind::TestModuleMarker),
            usize::from(marker),
            "{source:?}"
        );
        assert_eq!(
            declaration
                .children_with_tokens()
                .filter_map(|element| element.into_token())
                .filter(|token| token.kind() == SyntaxKind::Identifier)
                .map(|token| token.text().to_string())
                .collect::<Vec<_>>(),
            direct_names,
            "{source:?}"
        );
        assert_eq!(
            visibility
                .map(|kind| declaration.first_token().map(|token| token.kind()) == Some(kind)),
            visibility.map(|_| true),
            "{source:?}"
        );
    }
}

#[test]
fn mod_c10_keeps_dynamic_word_operator_names_raw() {
    let operators = OperatorTable::from_declarations([OperatorDeclaration::new(
        "dynamic",
        OperatorFixities::new().with_nullfix(),
    )])
    .expect("dynamic module-name operator table");
    let source = "mod dynamic;";
    let (green, exit) = run_statement_with(source, &operators);
    assert_eq!(green.to_string(), source);
    assert!(matches!(exit, Some(Err(Either::Right(_)))));
    let declaration = mod_declaration(&green);
    assert_eq!(descendants(&declaration, SyntaxKind::Error), 0);
    assert_eq!(descendants(&declaration, SyntaxKind::NullfixOperatorUse), 0);
    assert_eq!(
        declaration
            .children_with_tokens()
            .filter_map(|element| element.into_token())
            .filter(|token| token.kind() == SyntaxKind::Identifier)
            .map(|token| token.text().to_string())
            .collect::<Vec<_>>(),
        ["dynamic"],
    );
}

#[test]
fn mod_c10_dispatch_is_exact_and_irrevocable_after_mod() {
    for source in ["mod A;", "my mod A;", "our mod A;", "pub mod A;"] {
        let (green, _) = run_statement(source);
        assert_eq!(green.to_string(), source);
        mod_declaration(&green);
    }

    for source in ["module", "modular", "mod!", "my_mod"] {
        let (green, _) = run_statement(source);
        assert!(
            !SyntaxNode::new_root(green)
                .descendants()
                .any(|node| node.kind() == SyntaxKind::ModDeclaration),
            "{source:?}"
        );
    }

    let (green, _) = run_statement("my mod = value");
    let root = SyntaxNode::new_root(green);
    assert!(
        root.descendants()
            .any(|node| node.kind() == SyntaxKind::ModDeclaration)
    );
    assert!(
        !root
            .descendants()
            .any(|node| node.kind() == SyntaxKind::BindingStatement)
    );

    for source in ["my test = value", "my modular = value"] {
        let (green, _) = run_statement(source);
        let root = SyntaxNode::new_root(green);
        assert!(
            root.descendants()
                .any(|node| node.kind() == SyntaxKind::BindingStatement),
            "{source:?}"
        );
        assert!(
            !root
                .descendants()
                .any(|node| node.kind() == SyntaxKind::TestModuleMarker),
            "{source:?}"
        );
    }
}

#[test]
fn mod_c10_owns_only_its_three_body_forms_and_inline_terminal() {
    for source in [
        "mod Empty;",
        "mod Braced {x; my y = z; use p; mod Nested;}",
        "mod Inline: use p;",
        "mod Indented:\n  x\n  my y = z\n  use p\n  mod Nested;",
    ] {
        let (green, exit) = run_statement(source);
        assert_eq!(green.to_string(), source, "{source:?}");
        assert!(matches!(exit, Some(Err(Either::Right(_)))), "{source:?}");
    }

    let (green, _) = run_statement("mod Braced {x}");
    assert_eq!(
        descendants(
            &mod_declaration(&green),
            SyntaxKind::BracedStatementBlockExpression
        ),
        1
    );
    let (green, _) = run_statement("mod Indented:\n  x");
    assert_eq!(
        descendants(&mod_declaration(&green), SyntaxKind::IndentedStatementBlock),
        1
    );
    let (green, _) = run_statement("mod Inline: x;");
    let declaration = mod_declaration(&green);
    assert_eq!(
        declaration
            .children()
            .filter(|node| node.kind() == SyntaxKind::Statement)
            .count(),
        1
    );

    let source = "mod Name: my target = value;";
    let (green, exit) = run_statement(source);
    assert_eq!(green.to_string(), source);
    assert!(matches!(exit, Some(Err(Either::Right(_)))));
    let declaration = mod_declaration(&green);
    let statement = declaration
        .children()
        .find(|node| node.kind() == SyntaxKind::Statement)
        .expect("inline canonical Statement");
    let binding = statement
        .children()
        .find(|node| node.kind() == SyntaxKind::BindingStatement)
        .expect("inline BindingStatement");
    assert!(
        !binding
            .descendants_with_tokens()
            .filter_map(|element| element.into_token())
            .any(|token| token.kind() == SyntaxKind::Semicolon)
    );
    assert_eq!(
        declaration
            .children_with_tokens()
            .filter_map(|element| element.into_token())
            .filter(|token| token.kind() == SyntaxKind::Semicolon)
            .count(),
        1
    );
    assert_eq!(
        declaration
            .children_with_tokens()
            .filter_map(|element| element.into_token())
            .filter(|token| token.kind() == SyntaxKind::Semicolon)
            .count(),
        1
    );

    for (source, owned) in [
        ("mod A; next", "mod A;"),
        ("mod A {x}; next", "mod A {x}"),
        ("mod A:\n  x\n; next", "mod A:\n  x"),
    ] {
        let (green, exit) = run_statement(source);
        assert_eq!(green.to_string(), owned, "{source:?}");
        assert!(matches!(exit, Some(Err(Either::Left(_)))), "{source:?}");
    }
}

#[test]
fn mod_c10_applies_gmod_to_every_header_gap() {
    let source = "my\n  mod\n  test\n  suite\n  ;";
    let (green, exit) = run_statement(source);
    assert_eq!(green.to_string(), source);
    assert!(matches!(exit, Some(Err(Either::Right(_)))));
    let declaration = mod_declaration(&green);
    assert_eq!(descendants(&declaration, SyntaxKind::Missing), 0);
    assert_eq!(descendants(&declaration, SyntaxKind::Error), 0);

    for (source, owned) in [
        ("mod\nNext;", "mod"),
        ("mod A\nnext", "mod A"),
        ("mod test\nname;", "mod test"),
    ] {
        let (green, exit) = run_statement(source);
        assert_eq!(green.to_string(), owned, "{source:?}");
        assert!(matches!(
            exit,
            Some(Err(Either::Left(item)))
                if item.leading_view().has_ordinary_newline()
        ));
    }

    let (green, exit) = run_statement("my\nmod A;");
    assert_eq!(green.to_string(), "my");
    assert!(matches!(exit, Some(Err(Either::Left(_)))));
    assert!(
        !SyntaxNode::new_root(green)
            .descendants()
            .any(|node| node.kind() == SyntaxKind::ModDeclaration)
    );
}

#[test]
fn mod_c10_recovers_identity_once_without_body_cascade() {
    for (source, missing, error) in [
        ("mod", 1, 0),
        ("mod ;", 1, 0),
        ("mod : x", 1, 0),
        ("mod {}", 1, 0),
        ("mod @ Name;", 0, 1),
        ("mod @ ;", 0, 1),
        ("mod @", 0, 1),
        ("mod test", 1, 0),
        ("mod test @ Name;", 0, 1),
        ("mod test @ ;", 0, 1),
        ("mod test @", 0, 1),
    ] {
        let (green, exit) = run_statement(source);
        assert_eq!(green.to_string(), source, "{source:?}");
        assert!(matches!(exit, Some(Err(Either::Right(_)))), "{source:?}");
        let declaration = mod_declaration(&green);
        assert_eq!(
            descendants(&declaration, SyntaxKind::Missing),
            missing,
            "{source:?}"
        );
        assert_eq!(
            descendants(&declaration, SyntaxKind::Error),
            error,
            "{source:?}"
        );
    }

    let (green, _) = run_statement("mod test;");
    assert_eq!(
        descendants(&mod_declaration(&green), SyntaxKind::Missing),
        0
    );
}

#[test]
fn mod_c10_commits_ordinary_eof_trivia_before_the_owned_missing_slot() {
    for source in ["mod ", "mod A ", "mod test "] {
        let (green, exit) = run_statement(source);
        assert_eq!(green.to_string(), source, "{source:?}");
        assert!(matches!(exit, Some(Err(Either::Right(_)))), "{source:?}");
        let declaration = mod_declaration(&green);
        assert_eq!(
            descendants(&declaration, SyntaxKind::Missing),
            1,
            "{source:?}"
        );
        let topology = declaration
            .children_with_tokens()
            .map(|element| element.kind())
            .collect::<Vec<_>>();
        assert_eq!(
            &topology[topology.len() - 2..],
            [SyntaxKind::Whitespace, SyntaxKind::Missing],
            "{source:?}",
        );
    }
}

#[test]
fn mod_c10_recovers_body_slots_and_preserves_boundaries() {
    for (source, missing, error) in [
        ("mod A", 1, 0),
        ("mod A x", 1, 0),
        ("mod A\n  x", 1, 0),
        ("mod A @ x", 0, 1),
        ("mod A @", 0, 1),
        ("mod A: @ x;", 0, 1),
        ("mod A: @", 0, 1),
        ("mod A:", 1, 0),
        ("mod A::x", 0, 1),
        ("mod A][next", 0, 1),
        ("mod A {x", 1, 0),
    ] {
        let (green, exit) = run_statement(source);
        assert_eq!(green.to_string(), source, "{source:?}");
        assert!(matches!(exit, Some(Err(Either::Right(_)))), "{source:?}");
        let declaration = mod_declaration(&green);
        assert_eq!(
            descendants(&declaration, SyntaxKind::Missing),
            missing,
            "{source:?}"
        );
        assert_eq!(
            descendants(&declaration, SyntaxKind::Error),
            error,
            "{source:?}"
        );
    }

    for (source, owned, expected) in [
        ("mod A\nnext", "mod A", TokenKind::Identifier),
        ("mod A, next", "mod A", TokenKind::Comma),
        ("mod A:\nnext", "mod A:", TokenKind::Identifier),
    ] {
        let (green, exit) = run_statement(source);
        assert_eq!(green.to_string(), owned, "{source:?}");
        assert!(matches!(
            exit,
            Some(Err(Either::Left(item))) if token_kind(&item) == Some(expected)
        ));
    }

    let (green, _) = run_statement("mod A][next");
    let declaration = mod_declaration(&green);
    let error = declaration
        .children()
        .find(|node| node.kind() == SyntaxKind::Error)
        .expect("local BodyIntroducer Error");
    assert_eq!(error.text().to_string(), "][");

    let operators = OperatorTable::empty();
    let (green, exit) = run_statement_with_stops("mod A:  else", &operators, STOP_ELSE);
    assert_eq!(green.to_string(), "mod A:");
    let Some(Err(Either::Left(mut item))) = exit else {
        panic!("else must remain pending")
    };
    assert_eq!(
        item.payload_view().token_kind(),
        Some(TokenKind::Identifier)
    );
    assert_eq!(item.payload_view().spelling(), Some("else"));
    assert_eq!(emit_pending_leading_text(&mut item), "  ");

    let (green, exit) = run_statement("mod A @\n;");
    assert_eq!(green.to_string(), "mod A @");
    assert!(matches!(
        exit,
        Some(Err(Either::Left(item)))
            if token_kind(&item) == Some(TokenKind::Semicolon)
                && item.leading_view().has_ordinary_newline()
    ));
}

#[test]
fn mod_c10_reaches_shared_statement_sites_but_not_expression_only_sites() {
    for source in [
        "{mod A; x}",
        "f:\n  mod A;\n  x",
        "if c:\n  mod A;\n  x",
        "case x:\n  p ->\n    mod A;\n    x",
        "catch action:\n  err ->\n    mod A;\n    recover",
        "value with: mod A;",
        "value with:\n  mod A;\n  x",
        "{use {a\nmod B;}",
    ] {
        let (green, exit) = run(source);
        assert_eq!(green.to_string(), source, "{source:?}");
        assert!(matches!(exit, Some(Err(Either::Right(_)))), "{source:?}");
        assert!(
            SyntaxNode::new_root(green)
                .descendants()
                .any(|node| node.kind() == SyntaxKind::ModDeclaration),
            "{source:?}"
        );
    }

    let source = "my x =\n  mod A;\n  x";
    let (green, exit) = run_statement(source);
    assert_eq!(green.to_string(), source);
    assert!(matches!(exit, Some(Err(Either::Right(_)))));
    assert!(
        SyntaxNode::new_root(green)
            .descendants()
            .any(|node| node.kind() == SyntaxKind::ModDeclaration)
    );

    for source in [
        "mod Outer {mod Inner;}",
        "mod Outer:\n  mod Inner;",
        "mod Outer: mod Inner;",
    ] {
        let (green, exit) = run_statement(source);
        assert_eq!(green.to_string(), source, "{source:?}");
        assert!(matches!(exit, Some(Err(Either::Right(_)))), "{source:?}");
        assert_eq!(
            SyntaxNode::new_root(green)
                .descendants()
                .filter(|node| node.kind() == SyntaxKind::ModDeclaration)
                .count(),
            2,
            "{source:?}"
        );
    }

    for source in [
        "f: mod A;",
        "if c: mod A;",
        "case x: p -> mod A;",
        "catch action: err -> mod A;",
        "my x = mod A;",
    ] {
        let (green, _) = run(source);
        assert!(
            !SyntaxNode::new_root(green)
                .descendants()
                .any(|node| node.kind() == SyntaxKind::ModDeclaration),
            "{source:?}"
        );
    }
}
