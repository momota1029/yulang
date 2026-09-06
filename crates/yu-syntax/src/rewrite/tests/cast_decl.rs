use super::*;

fn declaration(green: &GreenNode) -> SyntaxNode {
    SyntaxNode::new_root(green.clone())
        .descendants()
        .find(|node| node.kind() == SyntaxKind::CastDeclaration)
        .expect("CastDeclaration")
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

fn pending_item(exit: Option<NormalizedExit>) -> Item {
    match exit {
        Some(NormalizedExit::Complete(Err(Either::Left(item)), _)) => item,
        Some(NormalizedExit::Complete(Err(Either::Right(end)), _)) => end.item,
        _ => panic!("Cast witness must return one pending Item"),
    }
}

#[test]
fn cast_private_owner_builds_bodyless_inline_and_indented_forms() {
    for (source, body, indented) in [
        ("cast(x: A): B;", 0, 0),
        ("pub cast(x: A): B = x", 1, 0),
        ("cast(x: A): B =\n  x", 1, 1),
    ] {
        let (green, exit, remainder) = run_cast_declaration(source, 0, 0, LineEntry::InLine, None);
        assert!(exit.is_some(), "{source:?}");
        assert_eq!(green.to_string(), source, "{source:?}");
        assert_eq!(remainder, "", "{source:?}");
        let declaration = declaration(&green);
        assert_eq!(
            count(&declaration, SyntaxKind::CastPattern),
            1,
            "{source:?}"
        );
        assert_eq!(count(&declaration, SyntaxKind::CastTarget), 1, "{source:?}");
        assert_eq!(
            count(&declaration, SyntaxKind::CastBody),
            body,
            "{source:?}"
        );
        assert_eq!(
            count(&declaration, SyntaxKind::IndentedStatementBlock),
            indented,
            "{source:?}"
        );
        assert_eq!(count(&declaration, SyntaxKind::Missing), 0, "{source:?}");
        assert_eq!(count(&declaration, SyntaxKind::Error), 0, "{source:?}");
    }

    let source = "pub cast(x: int): user_id = user_id { raw: x }";
    let (green, _, remainder) = run_cast_declaration(source, 0, 0, LineEntry::InLine, None);
    assert_eq!(green.to_string(), source);
    assert_eq!(remainder, "");
    let declaration = declaration(&green);
    assert_eq!(count(&declaration, SyntaxKind::CastBody), 1);
    assert!(count(&declaration, SyntaxKind::OperatorChain) >= 1);
    assert_eq!(
        count(&declaration, SyntaxKind::BracedStatementBlockExpression),
        1
    );
    assert_eq!(count(&declaration, SyntaxKind::Missing), 0);
    assert_eq!(count(&declaration, SyntaxKind::Error), 0);
    assert_eq!(
        declaration
            .children_with_tokens()
            .map(|element| element.kind())
            .collect::<Vec<_>>(),
        [
            SyntaxKind::PubKw,
            SyntaxKind::Whitespace,
            SyntaxKind::CastKw,
            SyntaxKind::CastPattern,
            SyntaxKind::CastTarget,
            SyntaxKind::Whitespace,
            SyntaxKind::Equals,
            SyntaxKind::CastBody,
        ]
    );
}

#[test]
fn cast_intro_is_exact_visibility_aware_and_isolated_from_dispatch() {
    for source in [
        "cast(x): T;",
        "my cast(x): T;",
        "our cast (x): T;",
        "pub cast(x): T;",
        "pub\n  cast\n    (x): T;",
    ] {
        let (green, exit, _) = run_cast_declaration(source, 0, 0, LineEntry::InLine, None);
        assert!(exit.is_some(), "{source:?}");
        assert_eq!(green.to_string(), source, "{source:?}");
        assert_eq!(token_count(&declaration(&green), SyntaxKind::CastKw), 1);
    }

    for source in [
        "casting(x): T;",
        "castaway(x): T;",
        "mycast(x): T;",
        "my castish(x): T;",
        "our\ncast(x): T;",
        "\ncast(x): T;",
    ] {
        let (green, exit, remainder) =
            run_cast_declaration(source, 0, 700, LineEntry::InLine, None);
        assert!(exit.is_none(), "{source:?}");
        assert_eq!(green.to_string(), "", "{source:?}");
        assert_eq!(remainder, source, "{source:?}");
    }

    let source = "my cast = value";
    let (green, exit, remainder) = run_cast_declaration(source, 0, 0, LineEntry::InLine, None);
    assert!(exit.is_some());
    assert_eq!(green.to_string(), source);
    assert_eq!(remainder, "");
    let declaration = declaration(&green);
    assert_eq!(count(&declaration, SyntaxKind::Missing), 1);
    assert_eq!(count(&declaration, SyntaxKind::BindingStatement), 0);
    assert_eq!(count(&declaration, SyntaxKind::CastBody), 1);

    let (green, _) = run_statement("cast(x): T;");
    assert_eq!(
        SyntaxNode::new_root(green)
            .descendants()
            .filter(|node| node.kind() == SyntaxKind::CastDeclaration)
            .count(),
        0
    );
}

#[test]
fn cast_pattern_reuses_full_pattern_surface_and_nested_close_handoffs() {
    for source in [
        "cast(:symbol): T;",
        "cast(x: Source): Target;",
        "cast({x = 1}): T;",
        "cast([x, ..rest]): T;",
        "cast((x | y)): T;",
    ] {
        let (green, _, remainder) = run_cast_declaration(source, 0, 0, LineEntry::InLine, None);
        assert_eq!(green.to_string(), source, "{source:?}");
        assert_eq!(remainder, "", "{source:?}");
        let declaration = declaration(&green);
        assert_eq!(count(&declaration, SyntaxKind::Missing), 0, "{source:?}");
        assert_eq!(count(&declaration, SyntaxKind::Error), 0, "{source:?}");
    }

    for source in ["cast([x): B;", "cast({x): B;", "cast(x: '[A): B;"] {
        let (green, _, remainder) = run_cast_declaration(source, 0, 0, LineEntry::InLine, None);
        assert_eq!(green.to_string(), source, "{source:?}");
        assert_eq!(remainder, "", "{source:?}");
        let declaration = declaration(&green);
        assert_eq!(count(&declaration, SyntaxKind::Missing), 1, "{source:?}");
        assert_eq!(count(&declaration, SyntaxKind::Error), 0, "{source:?}");
        assert_eq!(
            token_count(&declaration, SyntaxKind::RParen),
            1,
            "{source:?}"
        );
    }

    let source = "cast((x @): B;";
    let (green, _, remainder) = run_cast_declaration(source, 0, 0, LineEntry::InLine, None);
    assert_eq!(green.to_string(), source);
    assert_eq!(remainder, "");
    let declaration = declaration(&green);
    assert_eq!(count(&declaration, SyntaxKind::Missing), 1);
    assert_eq!(count(&declaration, SyntaxKind::Error), 1);
    assert_eq!(token_count(&declaration, SyntaxKind::RParen), 1);
}

#[test]
fn cast_target_reuses_full_type_surface_with_nested_form_punctuation_suspended() {
    for source in [
        "cast(x): List(Int)::Result Arg -> Out -> Final;",
        "cast(x): F(:{A});",
        "cast(x): [e] F [io] -> U;",
        "cast(x): {field: A};",
    ] {
        let (green, _, remainder) = run_cast_declaration(source, 0, 0, LineEntry::InLine, None);
        assert_eq!(green.to_string(), source, "{source:?}");
        assert_eq!(remainder, "", "{source:?}");
        let declaration = declaration(&green);
        assert_eq!(count(&declaration, SyntaxKind::CastTarget), 1, "{source:?}");
        assert_eq!(count(&declaration, SyntaxKind::Missing), 0, "{source:?}");
        assert_eq!(count(&declaration, SyntaxKind::Error), 0, "{source:?}");
        assert_eq!(
            token_count(&declaration, SyntaxKind::Semicolon),
            1,
            "{source:?}"
        );
    }
}

#[test]
fn cast_pattern_prefix_and_close_recovery_is_bounded() {
    for (source, missing, errors) in [
        ("cast;", 1, 0),
        ("cast();", 2, 0),
        ("cast(@): B;", 0, 1),
        ("cast(x @ ): B;", 0, 1),
        ("cast @ (x): B;", 0, 1),
        ("cast @ : B;", 0, 1),
        ("cast @ = value", 0, 1),
    ] {
        let (green, _, remainder) = run_cast_declaration(source, 0, 0, LineEntry::InLine, None);
        assert_eq!(green.to_string(), source, "{source:?}");
        assert_eq!(remainder, "", "{source:?}");
        let declaration = declaration(&green);
        assert_eq!(
            count(&declaration, SyntaxKind::Missing),
            missing,
            "{source:?}"
        );
        assert_eq!(count(&declaration, SyntaxKind::Error), errors, "{source:?}");
    }

    let source = "cast x ) tail";
    let (green, exit, remainder) = run_cast_declaration(
        source,
        stops_for(TokenKind::RParen),
        0,
        LineEntry::InLine,
        None,
    );
    assert_eq!(green.to_string(), "cast x");
    assert_eq!(remainder, " tail");
    let declaration = declaration(&green);
    assert_eq!(count(&declaration, SyntaxKind::Missing), 1);
    assert_eq!(count(&declaration, SyntaxKind::Error), 0);
    assert_eq!(token_count(&declaration, SyntaxKind::RParen), 0);
    let mut pending = pending_item(exit);
    assert_eq!(pending.payload_view().token_kind(), Some(TokenKind::RParen));
    assert_eq!(emit_pending_leading_text(&mut pending), " ");
}

#[test]
fn cast_target_and_form_recovery_keep_starters_distinct() {
    for (source, missing, errors, targets, bodies) in [
        ("cast(x) B;", 1, 0, 1, 0),
        ("cast(x) @ : B;", 0, 1, 1, 0),
        ("cast(x);", 1, 0, 0, 0),
        ("cast(x): ;", 1, 0, 1, 0),
        ("cast(x): @ ;", 0, 1, 1, 0),
        ("cast(x): B", 1, 0, 1, 0),
        ("cast(x): B = value", 0, 0, 1, 1),
        ("cast(x): B == value", 0, 1, 1, 0),
    ] {
        let (green, _, remainder) = run_cast_declaration(source, 0, 0, LineEntry::InLine, None);
        assert_eq!(green.to_string(), source, "{source:?}");
        assert_eq!(remainder, "", "{source:?}");
        let declaration = declaration(&green);
        assert_eq!(
            count(&declaration, SyntaxKind::Missing),
            missing,
            "{source:?}"
        );
        assert_eq!(count(&declaration, SyntaxKind::Error), errors, "{source:?}");
        assert_eq!(
            count(&declaration, SyntaxKind::CastTarget),
            targets,
            "{source:?}"
        );
        assert_eq!(
            count(&declaration, SyntaxKind::CastBody),
            bodies,
            "{source:?}"
        );
    }
}

#[test]
fn cast_definition_body_preserves_boundaries_and_recovers_one_run() {
    for source in [
        "cast(x): T = value: argument",
        "cast(x): T = value with: body",
        "cast(x): T = value { field: x }",
        "cast(x): T =\r\n  my y = x\r\n  y",
    ] {
        let (green, _, remainder) = run_cast_declaration(source, 0, 0, LineEntry::InLine, None);
        assert_eq!(green.to_string(), source, "{source:?}");
        assert_eq!(remainder, "", "{source:?}");
        let declaration = declaration(&green);
        assert_eq!(count(&declaration, SyntaxKind::Missing), 0, "{source:?}");
        assert_eq!(count(&declaration, SyntaxKind::Error), 0, "{source:?}");
    }

    let source = "cast(x): T = @ value";
    let (green, _, remainder) = run_cast_declaration(source, 0, 0, LineEntry::InLine, None);
    assert_eq!(green.to_string(), source);
    assert_eq!(remainder, "");
    let node = declaration(&green);
    assert_eq!(count(&node, SyntaxKind::Error), 1);
    assert_eq!(count(&node, SyntaxKind::Missing), 0);
    let source = "cast(x): T = @   ";
    let (green, _, remainder) = run_cast_declaration(source, 0, 0, LineEntry::InLine, None);
    assert_eq!(green.to_string(), source);
    assert_eq!(remainder, "");
    let node = declaration(&green);
    assert_eq!(count(&node, SyntaxKind::Error), 1);
    assert_eq!(count(&node, SyntaxKind::Missing), 0);
    assert_eq!(
        node.descendants()
            .find(|descendant| descendant.kind() == SyntaxKind::Error)
            .expect("PatternIntroducer Error")
            .to_string(),
        "@   "
    );

    let source = "cast(x): T = ; tail";
    let (green, exit, remainder) = run_cast_declaration(source, 0, 0, LineEntry::InLine, None);
    assert_eq!(green.to_string(), "cast(x): T = ");
    assert_eq!(remainder, " tail");
    assert_eq!(count(&declaration(&green), SyntaxKind::Missing), 1);
    let pending = pending_item(exit);
    assert_eq!(
        pending.payload_view().token_kind(),
        Some(TokenKind::Semicolon)
    );

    let source = "cast(x): T =\ny";
    let (green, exit, remainder) = run_cast_declaration(source, 0, 0, LineEntry::InLine, None);
    assert_eq!(green.to_string(), "cast(x): T =");
    assert_eq!(remainder, "");
    assert_eq!(count(&declaration(&green), SyntaxKind::Missing), 1);
    let mut pending = pending_item(exit);
    assert_eq!(pending.payload_view().spelling(), Some("y"));
    assert_eq!(emit_pending_leading_text(&mut pending), "\n");
}

#[test]
fn cast_phase_transitions_preserve_disallowed_newline_gaps() {
    for (source, accepted, pending_kind, leading, missing, errors) in [
        ("cast(x)\n;", "cast(x)", TokenKind::Semicolon, "\n", 1, 0),
        (
            "cast(x)\r\n;",
            "cast(x)",
            TokenKind::Semicolon,
            "\r\n",
            1,
            0,
        ),
        ("cast(x\n: T;", "cast(x", TokenKind::Colon, "\n", 1, 0),
        (
            "cast(x):\r\n= value",
            "cast(x):",
            TokenKind::Equals,
            "\r\n",
            1,
            0,
        ),
        (
            "cast(x):\n= value",
            "cast(x):",
            TokenKind::Equals,
            "\n",
            1,
            0,
        ),
        ("cast(@\n;", "cast(@", TokenKind::Semicolon, "\n", 0, 1),
        (
            "cast(x @\r\n: T;",
            "cast(x @",
            TokenKind::Colon,
            "\r\n",
            0,
            1,
        ),
        (
            "cast(x) @\n;",
            "cast(x) @",
            TokenKind::Semicolon,
            "\n",
            0,
            1,
        ),
    ] {
        let (green, exit, _) = run_cast_declaration(source, 0, 0, LineEntry::InLine, None);
        assert_eq!(green.to_string(), accepted, "{source:?}");
        let declaration = declaration(&green);
        assert_eq!(
            count(&declaration, SyntaxKind::Missing),
            missing,
            "{source:?}"
        );
        assert_eq!(count(&declaration, SyntaxKind::Error), errors, "{source:?}");
        let mut pending = pending_item(exit);
        assert_eq!(pending.payload_view().token_kind(), Some(pending_kind));
        assert_eq!(
            emit_pending_leading_text(&mut pending),
            leading,
            "{source:?}"
        );
    }

    for (source, missing) in [
        ("cast(x)\n  ;", 1),
        ("cast(x)\r\n  : T;", 0),
        ("cast(x):\n  = value", 1),
    ] {
        let (green, _, remainder) = run_cast_declaration(source, 0, 0, LineEntry::InLine, None);
        assert_eq!(green.to_string(), source, "{source:?}");
        assert_eq!(remainder, "", "{source:?}");
        let declaration = declaration(&green);
        assert_eq!(
            count(&declaration, SyntaxKind::Missing),
            missing,
            "{source:?}"
        );
        assert_eq!(count(&declaration, SyntaxKind::Error), 0, "{source:?}");
    }
}

#[test]
fn cast_malformed_pattern_introducer_owns_only_same_line_eof_trivia() {
    let source = "cast @   ";
    let (green, exit, remainder) = run_cast_declaration(source, 0, 0, LineEntry::InLine, None);
    assert_eq!(green.to_string(), source);
    assert_eq!(remainder, "");
    let node = declaration(&green);
    assert_eq!(count(&node, SyntaxKind::Error), 1);
    assert_eq!(count(&node, SyntaxKind::Missing), 0);
    assert_eq!(
        node.descendants()
            .find(|descendant| descendant.kind() == SyntaxKind::Error)
            .expect("PatternIntroducer Error")
            .to_string(),
        "@   "
    );
    let mut pending = pending_item(exit);
    assert!(pending.payload_view().is_eof());
    assert_eq!(emit_pending_leading_text(&mut pending), "");

    for source in ["cast @\n", "cast @\r\n  "] {
        let (green, exit, remainder) = run_cast_declaration(source, 0, 0, LineEntry::InLine, None);
        assert_eq!(green.to_string(), "cast @", "{source:?}");
        assert_eq!(remainder, "", "{source:?}");
        let declaration = declaration(&green);
        assert_eq!(count(&declaration, SyntaxKind::Error), 1, "{source:?}");
        assert_eq!(count(&declaration, SyntaxKind::Missing), 0, "{source:?}");
        assert_eq!(
            declaration
                .descendants()
                .find(|descendant| descendant.kind() == SyntaxKind::Error)
                .expect("PatternIntroducer Error")
                .to_string(),
            "@",
            "{source:?}"
        );
        let mut pending = pending_item(exit);
        assert!(pending.payload_view().is_eof());
        assert_eq!(
            emit_pending_leading_text(&mut pending),
            &source["cast @".len()..],
            "{source:?}"
        );
    }
}

#[test]
fn cast_local_and_ambient_close_authority_preserves_exact_items() {
    let source = "cast([x ) ) tail";
    let (green, exit, remainder) = run_cast_declaration(
        source,
        stops_for(TokenKind::RParen),
        0,
        LineEntry::InLine,
        None,
    );
    assert_eq!(green.to_string(), "cast([x )");
    assert_eq!(remainder, " tail");
    let node = declaration(&green);
    assert_eq!(count(&node, SyntaxKind::Missing), 2);
    assert_eq!(token_count(&node, SyntaxKind::RParen), 1);
    let mut pending = pending_item(exit);
    assert_eq!(pending.payload_view().token_kind(), Some(TokenKind::RParen));
    assert_eq!(emit_pending_leading_text(&mut pending), " ");

    let source = "cast([x } tail";
    let (green, exit, remainder) = run_cast_declaration(
        source,
        stops_for(TokenKind::RBrace),
        0,
        LineEntry::InLine,
        None,
    );
    assert_eq!(green.to_string(), "cast([x");
    assert_eq!(remainder, " tail");
    assert_eq!(count(&declaration(&green), SyntaxKind::Missing), 1);
    let mut pending = pending_item(exit);
    assert_eq!(pending.payload_view().token_kind(), Some(TokenKind::RBrace));
    assert_eq!(emit_pending_leading_text(&mut pending), " ");

    let source = "cast(x): T else tail";
    let (green, exit, remainder) =
        run_cast_declaration(source, STOP_ELSE, 0, LineEntry::InLine, None);
    assert_eq!(green.to_string(), "cast(x): T");
    assert_eq!(remainder, " tail");
    assert_eq!(count(&declaration(&green), SyntaxKind::Missing), 1);
    let mut pending = pending_item(exit);
    assert_eq!(pending.payload_view().spelling(), Some("else"));
    assert_eq!(emit_pending_leading_text(&mut pending), " ");
}

#[test]
fn cast_fence_and_origin_boundary_remain_outer_owned() {
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
    let origin = 12_000;
    let accepted = "> > cast(x): T";
    let source = format!("{accepted}\r\n> > ```\r\nouter");
    let (green, exit, remainder) =
        run_cast_declaration(&source, 0, origin, LineEntry::PhysicalStart, Some(&fence));
    assert_eq!(green.to_string(), accepted);
    assert_eq!(remainder, "> > ```\r\nouter");
    assert_eq!(count(&declaration(&green), SyntaxKind::Missing), 1);
    let boundary = pending_item(exit);
    let (leading, pending) = emit_terminal_leading_text(boundary);
    assert_eq!(leading, "\r\n");
    assert_eq!(pending.coordinate(), origin + accepted.len() + 2);
    assert!(matches!(
        pending.into_kind(),
        Boundary::BorrowedClose(BorrowedTarget::YumarkFence(_))
    ));

    let accepted = "> > cast @";
    let source = format!("{accepted}\r\n> > ```\r\nouter");
    let (green, exit, remainder) =
        run_cast_declaration(&source, 0, origin, LineEntry::PhysicalStart, Some(&fence));
    assert_eq!(green.to_string(), accepted);
    assert_eq!(remainder, "> > ```\r\nouter");
    let declaration = declaration(&green);
    assert_eq!(count(&declaration, SyntaxKind::Error), 1);
    assert_eq!(count(&declaration, SyntaxKind::Missing), 0);
    let boundary = pending_item(exit);
    let (leading, pending) = emit_terminal_leading_text(boundary);
    assert_eq!(leading, "\r\n");
    assert!(matches!(
        pending.into_kind(),
        Boundary::BorrowedClose(BorrowedTarget::YumarkFence(_))
    ));
}
