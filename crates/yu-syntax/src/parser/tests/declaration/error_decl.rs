use crate::parser::tests::support::*;

fn declaration(green: &GreenNode) -> SyntaxNode {
    SyntaxNode::new_root(green.clone())
        .descendants()
        .find(|node| node.kind() == SyntaxKind::ErrorDeclaration)
        .expect("ErrorDeclaration")
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
    let error = node
        .descendants()
        .find(|child| child.kind() == SyntaxKind::Error)
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
        crate::parser::input::operator::STOP_WITH,
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
