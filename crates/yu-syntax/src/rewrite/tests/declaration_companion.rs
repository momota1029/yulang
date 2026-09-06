use super::*;

use crate::rewrite::{
    driver::Either,
    item::{BorrowedTarget, Boundary},
    operator::stops_for,
    yumark::{FenceOpener, FencePrefixPolicy},
};

fn syntax_root(green: GreenNode) -> SyntaxNode {
    SyntaxNode::new_root(green)
}

fn count(root: &SyntaxNode, kind: SyntaxKind) -> usize {
    root.descendants()
        .filter(|node| node.kind() == kind)
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

    let (green, _, _) =
        run_declaration_companion("with: derives", 0, 0, 0, LineEntry::InLine, None);
    let root = syntax_root(green);
    assert_eq!(count(&root, SyntaxKind::Statement), 1);
    assert_eq!(count(&root, SyntaxKind::DerivesClause), 0);
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
    assert_eq!(green.to_string(), "with @// : { item");
    assert_eq!(remainder, " item");
    let root = syntax_root(green);
    assert_eq!(count(&root, SyntaxKind::Error), 1, "{root:#?}");
    assert_eq!(count(&root, SyntaxKind::Missing), 0, "{root:#?}");
    assert_eq!(count(&root, SyntaxKind::Statement), 0, "{root:#?}");
    let mut item = pending(exit.expect("committed companion"));
    assert_eq!(item.payload_view().token_kind(), Some(TokenKind::Colon));
    assert_eq!(emit_pending_leading_text(&mut item), "\n");
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
    let source = "> > with:\r\n> >   item\r\n> > ```\r\nouter";
    let accepted = "> > with:\r\n> >   item";
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
    assert_eq!(count(&root, SyntaxKind::DerivesClause), 0);
}
