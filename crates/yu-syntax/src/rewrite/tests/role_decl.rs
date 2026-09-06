use super::*;

fn declaration(green: &GreenNode) -> SyntaxNode {
    SyntaxNode::new_root(green.clone())
        .descendants()
        .find(|node| node.kind() == SyntaxKind::RoleDeclaration)
        .expect("RoleDeclaration")
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
        "role F (A -> B) 't;",
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
        let error = node
            .descendants()
            .find(|child| child.kind() == SyntaxKind::Error)
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

    for (source, error_text) in [("role R @   ", "@   "), ("role R: @   ", " @   ")] {
        let (green, _, remainder) = run_role_declaration(source, 0, 0, LineEntry::InLine, None);
        assert_eq!(green.to_string(), source, "{source:?}");
        assert_eq!(remainder, "", "{source:?}");
        let node = declaration(&green);
        assert_eq!(count(&node, SyntaxKind::Error), 1, "{source:?}\n{node:#?}");
        assert_eq!(
            count(&node, SyntaxKind::Missing),
            0,
            "{source:?}\n{node:#?}"
        );
        let error = node
            .descendants()
            .find(|child| child.kind() == SyntaxKind::Error)
            .expect("one malformed body run");
        assert_eq!(
            error.text().to_string(),
            error_text,
            "{source:?}\n{node:#?}"
        );
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
    assert_eq!(green.to_string(), "role R: ");
    assert_eq!(remainder, "");
    let node = declaration(&green);
    assert_eq!(count(&node, SyntaxKind::Missing), 1, "{node:#?}");
    let whitespace = node
        .children_with_tokens()
        .filter_map(|element| element.into_token())
        .filter(|token| token.kind() == SyntaxKind::Whitespace)
        .last()
        .expect("colon-body local gap");
    let missing = node
        .descendants()
        .find(|child| child.kind() == SyntaxKind::Missing)
        .expect("missing Role body");
    assert_eq!(whitespace.text(), " ");
    assert_eq!(whitespace.text_range().end(), missing.text_range().start());
    assert_eq!(
        pending_token_leading(exit, TokenKind::Semicolon, ";", LineEntry::InLine),
        []
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
        super::super::operator::STOP_ELSE,
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
        super::super::operator::STOP_ELSE,
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
        super::super::operator::STOP_ELSE,
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
        super::super::operator::STOP_ELSE,
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
