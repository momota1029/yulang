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
