use crate::parser::tests::support::*;

#[test]
fn impl_first_colon_absence_is_description_without_body_cascade() {
    use crate::session::{DeclarationRole, ExpectedSyntax, GrammarRole, ImplRole, RecoveryKind};
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
    use crate::parser::input::yumark::{FenceOpener, FencePrefixPolicy};
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
        if records[0].kind == crate::session::RecoveryKind::Missing {
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
    use crate::session::{BindingRole, DeclarationRole, GrammarRole, ImplRole};
    for (source, role) in [
        (
            "impl @ ;",
            GrammarRole::Type(crate::session::TypeRole::Primary),
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
    let mut recover = Recover::new(&operators);
    let mut builder = frozen.map_or_else(GreenNodeBuilder::new, GreenNodeBuilder::reconcile);
    builder.start_node(SyntaxKind::Root.into());
    let exit = impl_declaration_witness(
        In::new(&mut input, &mut recover, &mut builder),
        0,
        stops,
        crate::parser::statement::StatementLineHandoff::OrdinaryLayout,
        100,
        LineEntry::InLine,
        fence,
    );
    builder.finish_node();
    let (green, records) = builder.finish_with_recoveries();
    (green, exit, records, input)
}

#[test]
fn impl_body_introducer_eof_retains_equal_indent_newline() {
    use crate::session::{DeclarationRole, GrammarRole, ImplRole, RecoveryKind};
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
    use crate::session::{
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
    let error = node
        .descendants()
        .find(|child| child.kind() == SyntaxKind::Error)
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

    let lbrace_stop = crate::parser::input::operator::STOP_LBRACE;
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
        crate::parser::input::operator::STOP_ELSE,
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

    use crate::parser::input::item::{BorrowedTarget, Boundary, StopKind};
    use crate::parser::input::yumark::{FenceOpener, FencePrefixPolicy, QuoteTransitionKind};
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
