use crate::tests::support::*;

fn count(root: &SyntaxNode, kind: SyntaxKind) -> usize {
    if kind == SyntaxKind::Error {
        return crate::tests::recovery_output::recovery_groups(root).len();
    }
    root.descendants()
        .filter(|node| node.kind() == kind)
        .count()
}

fn assert_statement_family(source: &str, family: SyntaxKind) {
    let (green, exit) = run_statement(source);
    assert_eq!(green.to_string(), source, "{source:?}");
    assert!(exit.is_some(), "{source:?}");
    let root = SyntaxNode::new_root(green);
    let declaration = root
        .descendants()
        .find(|node| node.kind() == family)
        .unwrap_or_else(|| panic!("{family:?} for {source:?}"));
    assert_eq!(
        declaration.parent().map(|node| node.kind()),
        Some(SyntaxKind::Statement),
        "{source:?}",
    );
    assert_eq!(count(&root, family), 1, "{source:?}");
}

#[test]
fn canonical_statement_dispatches_each_added_declaration_family() {
    for (source, family) in [
        ("enum E;", SyntaxKind::EnumDeclaration),
        ("pub enum E;", SyntaxKind::EnumDeclaration),
        ("error E;", SyntaxKind::ErrorDeclaration),
        ("pub error E;", SyntaxKind::ErrorDeclaration),
        ("role R;", SyntaxKind::RoleDeclaration),
        ("pub role R;", SyntaxKind::RoleDeclaration),
        ("impl T;", SyntaxKind::ImplDeclaration),
        ("pub impl T;", SyntaxKind::ImplDeclaration),
        ("cast(x): T;", SyntaxKind::CastDeclaration),
        ("pub cast(x): T;", SyntaxKind::CastDeclaration),
        ("act A;", SyntaxKind::ActDeclaration),
        ("pub act A;", SyntaxKind::ActDeclaration),
    ] {
        assert_statement_family(source, family);
    }
}

#[test]
fn canonical_statement_keeps_visibility_collisions_with_their_existing_owner() {
    for (source, family) in [
        ("my enum E;", SyntaxKind::EnumDeclaration),
        ("my error E;", SyntaxKind::ErrorDeclaration),
        ("my act A;", SyntaxKind::ActDeclaration),
        ("my cast = value", SyntaxKind::CastDeclaration),
        ("my enum = value", SyntaxKind::BindingStatement),
        ("my error = value", SyntaxKind::BindingStatement),
        ("my act = value", SyntaxKind::BindingStatement),
        ("my enumx = value", SyntaxKind::BindingStatement),
        ("my rolex = value", SyntaxKind::BindingStatement),
        ("my castaway = value", SyntaxKind::BindingStatement),
    ] {
        assert_statement_family(source, family);
    }

    // Neither declaration claims Equals as a boundary of its required Type head.
    assert_statement_family("my role = value", SyntaxKind::RoleDeclaration);
    assert_statement_family("my impl = value", SyntaxKind::ImplDeclaration);

    for source in ["enumx", "errors", "roles", "implicit", "casting", "active"] {
        let (green, _) = run_statement(source);
        assert_eq!(green.to_string(), source, "{source:?}");
        let root = SyntaxNode::new_root(green);
        assert_eq!(count(&root, SyntaxKind::OperatorChain), 1, "{source:?}");
        assert_eq!(count(&root, SyntaxKind::EnumDeclaration), 0, "{source:?}");
        assert_eq!(count(&root, SyntaxKind::ErrorDeclaration), 0, "{source:?}");
        assert_eq!(count(&root, SyntaxKind::RoleDeclaration), 0, "{source:?}");
        assert_eq!(count(&root, SyntaxKind::ImplDeclaration), 0, "{source:?}");
        assert_eq!(count(&root, SyntaxKind::CastDeclaration), 0, "{source:?}");
        assert_eq!(count(&root, SyntaxKind::ActDeclaration), 0, "{source:?}");
    }
}

#[test]
fn canonical_statement_uses_shared_raw_heads_and_coordinated_fallback_order() {
    for (source, family) in [
        ("my error _hidden = A", SyntaxKind::ErrorDeclaration),
        ("my act $hidden = value", SyntaxKind::ActDeclaration),
        ("my act 'hidden = value", SyntaxKind::ActDeclaration),
        ("my enum = 1", SyntaxKind::BindingStatement),
        ("my error = 1", SyntaxKind::BindingStatement),
        ("my act = 1", SyntaxKind::BindingStatement),
        ("my use path", SyntaxKind::UseDeclaration),
        ("my use = value", SyntaxKind::BindingStatement),
        ("use", SyntaxKind::UseDeclaration),
        ("our use", SyntaxKind::UseDeclaration),
        ("pub use", SyntaxKind::UseDeclaration),
        ("my mod", SyntaxKind::ModDeclaration),
        ("my for = value", SyntaxKind::BindingStatement),
    ] {
        assert_statement_family(source, family);
    }
}

#[test]
fn canonical_statement_sigil_head_admission_keeps_raw_name_recovery_local() {
    for (source, accepted, family) in [
        (
            "my enum $hidden = A",
            "my enum $hidden",
            SyntaxKind::EnumDeclaration,
        ),
        (
            "my enum 'hidden = A",
            "my enum 'hidden",
            SyntaxKind::EnumDeclaration,
        ),
        (
            "my error &hidden = A",
            "my error &hidden",
            SyntaxKind::ErrorDeclaration,
        ),
    ] {
        let (green, exit) = run_statement(source);
        assert_eq!(green.to_string(), accepted, "{source:?}");
        let Some(Err(Either::Left(mut pending))) = exit else {
            panic!("the malformed Name must return its exact body starter: {source:?}")
        };
        assert_eq!(pending.payload_view().token_kind(), Some(TokenKind::Equals));
        assert_eq!(emit_pending_leading_text(&mut pending), " ");
        let root = SyntaxNode::new_root(green);
        assert_eq!(count(&root, family), 1, "{source:?}");
        assert_eq!(count(&root, SyntaxKind::Error), 1, "{source:?}");
        assert_eq!(count(&root, SyntaxKind::Missing), 0, "{source:?}");
    }
}

#[test]
fn canonical_statement_retry_keeps_the_item_with_its_single_admission() {
    let source = "{ @ my enum E = A }";
    let (green, _) = run(source);
    assert_eq!(green.to_string(), source);
    let root = SyntaxNode::new_root(green);
    let block = root
        .descendants()
        .find(|node| node.kind() == SyntaxKind::BracedStatementBlockExpression)
        .expect("braced canonical Statement sequence");
    assert_eq!(count(&block, SyntaxKind::Statement), 1);
    assert_eq!(count(&block, SyntaxKind::EnumDeclaration), 1);
    assert_eq!(count(&block, SyntaxKind::Error), 1);
}

#[test]
fn canonical_statement_preserves_existing_family_and_expression_order() {
    for (source, family) in [
        ("struct S;", SyntaxKind::StructDeclaration),
        ("type T = U", SyntaxKind::TypeDeclaration),
        ("use std::data", SyntaxKind::UseDeclaration),
        ("mod M;", SyntaxKind::ModDeclaration),
        ("for x in xs: x", SyntaxKind::ForStatement),
        ("my x = value", SyntaxKind::BindingStatement),
    ] {
        assert_statement_family(source, family);
    }

    let (green, _) = run_statement("value");
    let root = SyntaxNode::new_root(green);
    assert_eq!(root.to_string(), "value");
    assert_eq!(count(&root, SyntaxKind::OperatorChain), 1);

    let operators = dynamic_operator_table();
    for (source, operator) in [
        ("~value", SyntaxKind::PrefixOperatorUse),
        ("?", SyntaxKind::NullfixOperatorUse),
    ] {
        let (green, _) = run_statement_with(source, &operators);
        assert_eq!(green.to_string(), source, "{source:?}");
        let root = SyntaxNode::new_root(green);
        assert_eq!(count(&root, operator), 1, "{source:?}");
        assert_eq!(count(&root, SyntaxKind::OperatorChain), 1, "{source:?}");
    }
}

#[test]
fn canonical_statement_dispatch_composes_in_braced_and_indented_sequences() {
    let source = "{ enum E; error X; role R; }";
    let (green, exit) = run(source);
    assert_eq!(green.to_string(), source);
    assert!(matches!(exit, Some(Err(Either::Right(_)))));
    let root = SyntaxNode::new_root(green);
    let block = root
        .descendants()
        .find(|node| node.kind() == SyntaxKind::BracedStatementBlockExpression)
        .expect("braced statement block");
    assert_eq!(
        block
            .children()
            .filter(|node| node.kind() == SyntaxKind::Statement)
            .count(),
        3,
    );
    assert_eq!(count(&block, SyntaxKind::EnumDeclaration), 1);
    assert_eq!(count(&block, SyntaxKind::ErrorDeclaration), 1);
    assert_eq!(count(&block, SyntaxKind::RoleDeclaration), 1);

    let source = "if condition:\n  impl T;\n  cast(x): T;\nout";
    let (green, exit) = run(source);
    assert_eq!(green.to_string(), "if condition:\n  impl T;\n  cast(x): T;");
    let root = SyntaxNode::new_root(green);
    let block = root
        .descendants()
        .find(|node| node.kind() == SyntaxKind::IndentedStatementBlock)
        .expect("indented statement block");
    assert_eq!(
        block
            .children()
            .filter(|node| node.kind() == SyntaxKind::Statement)
            .count(),
        2,
    );
    assert_eq!(count(&block, SyntaxKind::ImplDeclaration), 1);
    assert_eq!(count(&block, SyntaxKind::CastDeclaration), 1);
    let Some(Err(Either::Left(mut pending))) = exit else {
        panic!("dedented statement must remain pending")
    };
    assert_eq!(pending.payload_view().spelling(), Some("out"));
    assert_eq!(emit_pending_leading_text(&mut pending), "\n");
}

#[test]
fn canonical_statement_dispatch_preserves_normalized_fence_boundary() {
    use crate::lexical::{
        item::{BorrowedTarget, Boundary},
        yumark::{FenceOpener, FencePrefixPolicy},
    };

    let fence = FenceBoundary {
        opener: FenceOpener {
            line: 0,
            marker: 0..3,
            marker_width: 3,
        },
        prefix_policy: FencePrefixPolicy::ActivePrefixQuote { depth: 2, base: 0 },
        close_column: 0,
    };
    let origin = 31_000;
    let accepted = "> > act A;";
    let source = format!("{accepted}\r\n> > ```\r\nouter");
    let (green, exit, remainder) =
        run_statement_normalized(&source, origin, LineEntry::PhysicalStart, Some(&fence));
    assert_eq!(green.to_string(), accepted);
    assert_eq!(remainder, "> > ```\r\nouter");
    let NormalizedExit::Complete(Err(Either::Left(boundary)), LineEntry::PhysicalStart) = exit
    else {
        panic!("Act statement must return the exact fence boundary")
    };
    let (leading, boundary) = emit_terminal_leading_text(boundary);
    assert_eq!(leading, "\r\n");
    assert_eq!(boundary.coordinate(), origin + accepted.len() + 2);
    assert!(matches!(
        boundary.into_kind(),
        Boundary::BorrowedClose(BorrowedTarget::YumarkFence(_))
    ));
}

#[test]
fn postfix_if_wraps_statement_expression() {
    let (green, _) = run_statement("x if c");
    assert_eq!(green.to_string(), "x if c");
    let root = SyntaxNode::new_root(green);
    let guard = root
        .descendants()
        .find(|n| n.kind() == SyntaxKind::PostfixIfExpression)
        .expect("postfix if");
    let children: Vec<_> = guard.children().map(|n| n.kind()).collect();
    assert_eq!(children, [SyntaxKind::OperatorChain, SyntaxKind::Condition]);
    assert_eq!(guard.parent().unwrap().kind(), SyntaxKind::Statement);
}

#[test]
fn postfix_if_wraps_pipeline() {
    let operators = OperatorTable::from_declarations([OperatorDeclaration::new(
        "|",
        OperatorFixities::new().with_infix(BindingPower::scalar(1), BindingPower::new(1, [1])),
    )])
    .unwrap();
    let (green, _) = run_statement_with("x | f if c", &operators);
    assert_eq!(green.to_string(), "x | f if c");
    let root = SyntaxNode::new_root(green);
    let guard = root
        .descendants()
        .find(|n| n.kind() == SyntaxKind::PostfixIfExpression)
        .unwrap();
    let operand = guard.children().next().unwrap();
    assert_eq!(operand.to_string(), "x | f");
    assert_eq!(operand.kind(), SyntaxKind::OperatorChain);
}

#[test]
fn postfix_if_wraps_inline_body_owners() {
    for (source, operand) in [
        ("say: value if c", "say: value"),
        ("for x in xs: last if done", "for x in xs: last"),
        ("if a: b if c", "if a: b"),
    ] {
        let (green, _) = run_statement(source);
        assert_eq!(green.to_string(), source, "{source}");
        let root = SyntaxNode::new_root(green);
        let guard = root
            .descendants()
            .find(|n| n.kind() == SyntaxKind::PostfixIfExpression)
            .unwrap_or_else(|| panic!("missing postfix if: {source}"));
        assert_eq!(
            guard.children().next().unwrap().to_string(),
            operand,
            "{source}"
        );
    }
}

#[test]
fn postfix_if_full_conditions_and_early_exits() {
    let ops = OperatorTable::from_declarations([
        OperatorDeclaration::new(
            "<",
            OperatorFixities::new().with_infix(BindingPower::scalar(5), BindingPower::new(5, [1])),
        ),
        OperatorDeclaration::new(
            "+",
            OperatorFixities::new().with_infix(BindingPower::scalar(5), BindingPower::new(5, [1])),
        ),
        OperatorDeclaration::new(
            "and",
            OperatorFixities::new().with_infix(BindingPower::scalar(5), BindingPower::new(5, [1])),
        ),
        OperatorDeclaration::new(
            "not",
            OperatorFixities::new().with_prefix(BindingPower::scalar(5)),
        ),
    ])
    .unwrap();
    for (source, operand, condition) in [
        ("x if 6 < 7", "x", "6 < 7"),
        ("say: 1 + 2 + 3 if 6 < 7", "say: 1 + 2 + 3", "6 < 7"),
        ("x if a and b", "x", "a and b"),
        ("x if f y", "x", "f y"),
        ("x if not done", "x", "not done"),
        ("return x if c", "return x", "c"),
        ("last 'outer if done", "last 'outer", "done"),
        ("next if skip", "next", "skip"),
    ] {
        let (green, _) = run_statement_with(source, &ops);
        assert_eq!(green.to_string(), source, "{source}");
        let root = SyntaxNode::new_root(green);
        let guard = root
            .descendants()
            .find(|n| n.kind() == SyntaxKind::PostfixIfExpression)
            .unwrap_or_else(|| panic!("{source}"));
        let mut children = guard.children();
        assert_eq!(children.next().unwrap().to_string(), operand, "{source}");
        assert_eq!(children.next().unwrap().to_string(), condition, "{source}");
    }
}

#[test]
fn postfix_if_chains_left_and_recovers_missing_condition() {
    let (green, _) = run_statement("a if b if c");
    let root = SyntaxNode::new_root(green);
    let guards: Vec<_> = root
        .descendants()
        .filter(|n| n.kind() == SyntaxKind::PostfixIfExpression)
        .collect();
    assert_eq!(guards.len(), 2);
    assert_eq!(guards[0].children().next().unwrap(), guards[1]);
    let (green, _) = run_statement("x if");
    assert_eq!(green.to_string(), "x if");
    assert_eq!(
        structural_facts(&green),
        vec![(crate::structural_diagnostic::StructuralKind::Missing, 4..4)]
    );
    let root = SyntaxNode::new_root(green);
    let missing = root
        .descendants()
        .find(|n| n.kind() == SyntaxKind::Missing)
        .unwrap();
    assert!(
        missing
            .ancestors()
            .any(|n| n.kind() == SyntaxKind::Condition)
    );
}

#[test]
fn postfix_if_in_delimited_expressions() {
    for source in ["(x if c)", "[x if c, y]"] {
        let text: std::sync::Arc<crate::SourceText> = std::sync::Arc::from(source);
        let parsed = crate::parse_file(
            text.clone(),
            std::sync::Arc::new(crate::scan_header(text)),
            std::sync::Arc::new(crate::SyntaxEnvironment::empty()),
        );
        assert_eq!(parsed.green().to_string(), source);
        assert_eq!(
            SyntaxNode::new_root(parsed.green().clone())
                .descendants()
                .filter(|n| n.kind() == SyntaxKind::PostfixIfExpression)
                .count(),
            1,
            "{source}"
        );
    }
}

fn parse_postfix_file(source: &str) -> GreenNode {
    let text: std::sync::Arc<crate::SourceText> = std::sync::Arc::from(source);
    crate::parse_file(
        text.clone(),
        std::sync::Arc::new(crate::scan_header(text)),
        std::sync::Arc::new(crate::SyntaxEnvironment::empty()),
    )
    .green()
    .clone()
}

#[test]
fn postfix_if_statement_and_closing_boundaries() {
    for source in [
        "a if c\nb",
        "a if c; b",
        "(x if c)",
        "[x if c, y]",
        "{x if c}",
    ] {
        let green = parse_postfix_file(source);
        assert_eq!(green.to_string(), source);
        assert!(
            structural_facts(&green).is_empty(),
            "{source}: {:?}",
            structural_facts(&green)
        );
        assert_eq!(
            SyntaxNode::new_root(green)
                .descendants()
                .filter(|n| n.kind() == SyntaxKind::PostfixIfExpression)
                .count(),
            1,
            "{source}"
        );
    }
}

#[test]
fn postfix_if_does_not_change_prefix_forms() {
    for source in [
        "if c: x",
        "if c { x } else { y }",
        "if a: b else: c",
        "if a: b elsif c: d else: e",
        "if a: if b: c else: d else: e",
    ] {
        let green = parse_postfix_file(source);
        assert_eq!(green.to_string(), source);
        assert!(
            structural_facts(&green).is_empty(),
            "{source}: {:?}",
            structural_facts(&green)
        );
        assert_eq!(
            SyntaxNode::new_root(green)
                .descendants()
                .filter(|n| n.kind() == SyntaxKind::PostfixIfExpression)
                .count(),
            0,
            "{source}"
        );
    }
}

#[test]
fn postfix_if_rejects_else_colon_and_brace() {
    for (source, range) in [
        ("x if c else: y", 7..14),
        ("x if c:", 6..7),
        ("x if c {", 7..8),
    ] {
        let green = parse_postfix_file(source);
        assert_eq!(green.to_string(), source);
        assert_eq!(
            structural_facts(&green),
            vec![(
                crate::structural_diagnostic::StructuralKind::ErrorGroup,
                range
            )],
            "{source}"
        );
        let root = SyntaxNode::new_root(green);
        let guard = root
            .descendants()
            .find(|n| n.kind() == SyntaxKind::PostfixIfExpression)
            .unwrap_or_else(|| panic!("missing guard: {source}"));
        assert!(
            !guard.descendants().any(|n| n.kind() == SyntaxKind::ElseArm),
            "{source}"
        );
    }
}

#[test]
fn postfix_if_is_a_binding_body_expression() {
    let source = "my result = x if c";
    let green = parse_postfix_file(source);
    assert_eq!(green.to_string(), source);
    assert!(structural_facts(&green).is_empty());
    let root = SyntaxNode::new_root(green);
    let guard = root
        .descendants()
        .find(|n| n.kind() == SyntaxKind::PostfixIfExpression)
        .unwrap();
    assert_eq!(guard.to_string(), "x if c");
    assert!(
        guard
            .ancestors()
            .any(|n| n.kind() == SyntaxKind::BindingStatement)
    );
}
