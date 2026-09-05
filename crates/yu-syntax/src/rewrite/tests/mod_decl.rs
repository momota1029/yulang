use super::*;

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
