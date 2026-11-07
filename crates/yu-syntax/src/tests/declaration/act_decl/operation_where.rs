use crate::tests::support::*;
use std::sync::Arc;

fn parse(source: &str) -> crate::ParsedFile {
    let text: Arc<crate::SourceText> = Arc::from(source);
    let parsed = crate::parse_file(
        Arc::clone(&text),
        Arc::new(crate::scan_header(text)),
        Arc::new(crate::SyntaxEnvironment::empty()),
    );
    assert_eq!(parsed.green().to_string(), source);
    parsed
}

fn clean(source: &str) -> SyntaxNode {
    let parsed = parse(source);
    assert!(parsed.structural_recoveries().is_empty(), "{source:?}");
    assert!(
        parsed.syntax_diagnostics().unwrap().is_empty(),
        "{source:?}"
    );
    SyntaxNode::new_root(parsed.green().clone())
}

fn children(node: &SyntaxNode) -> Vec<(SyntaxKind, String)> {
    node.children_with_tokens()
        .map(|child| (child.kind(), child.to_string()))
        .collect()
}

fn assert_clause(clause: &SyntaxNode, subject: &str, role: &str) {
    use SyntaxKind::*;
    assert_eq!(
        children(clause),
        [
            (WhereKw, "where".into()),
            (TypeExpression, format!(" {subject}")),
            (Colon, ":".into()),
            (TypeExpression, format!(" {role}")),
        ]
    );
    assert_eq!(clause.parent().unwrap().kind(), BindingStatement);
    assert_eq!(clause.children().count(), 2);
}

#[test]
fn operation_where_is_the_last_member_child_after_the_signature_header() {
    use SyntaxKind::*;
    let source = "act a:\n    our log: 'b -> ()\n        where 'b: Display\n";
    let root = clean(source);
    let operation = root
        .descendants()
        .find(|n| n.kind() == BindingStatement)
        .unwrap();
    assert_eq!(
        children(&operation),
        [
            (BindingHeader, "our log: 'b -> ()".into()),
            (Newline, "\n".into()),
            (Whitespace, "        ".into()),
            (WhereClause, "where 'b: Display".into()),
        ]
    );
    let header = operation.first_child().unwrap();
    assert_eq!(
        children(&header),
        [
            (OurKw, "our".into()),
            (Whitespace, " ".into()),
            (Pattern, "log: 'b -> ()".into()),
        ]
    );
    let annotation = header
        .descendants()
        .find(|n| n.kind() == PatternTypeAnnotation)
        .unwrap();
    assert_eq!(
        children(&annotation),
        [
            (Colon, ":".into()),
            (Whitespace, " ".into()),
            (TypeExpression, "'b -> ()".into()),
        ]
    );
    assert_clause(&operation.last_child().unwrap(), "'b", "Display");
    assert_eq!(root.last_child_or_token().unwrap().kind(), Newline);
}

#[test]
fn operation_where_leaves_the_following_member_in_the_act_body() {
    use SyntaxKind::*;
    for prefix in ["act a:", "act a 'x:", "pub host act a 'x:"] {
        let source = format!(
            "{prefix}\n    our log: 'b -> ()\n        where 'b: Display\n    our other: () -> ()\n"
        );
        let root = clean(&source);
        let body = root
            .descendants()
            .find(|n| n.kind() == IndentedStatementBlock)
            .unwrap();
        let members = body
            .children()
            .filter(|n| n.kind() == Statement)
            .collect::<Vec<_>>();
        assert_eq!(members.len(), 2);
        let first = members[0].first_child().unwrap();
        let second = members[1].first_child().unwrap();
        assert_eq!(first.kind(), BindingStatement);
        assert_eq!(second.kind(), BindingStatement);
        assert_eq!(second.to_string(), "our other: () -> ()");
        assert_eq!(
            children(&second),
            [(BindingHeader, "our other: () -> ()".into())]
        );
        assert_clause(&first.last_child().unwrap(), "'b", "Display");
        assert_eq!(first.last_child().unwrap().parent(), Some(first.clone()));
    }
}

#[test]
fn operation_multiple_constraints_use_the_binding_repeated_where_form() {
    use SyntaxKind::*;
    let source = "act a:\n    our log: ('a, 'b) -> ()\n        where 'a: Show\n        where 'b: Display\n    our other: () -> ()\n";
    let root = clean(source);
    let operation = root
        .descendants()
        .find(|n| n.kind() == BindingStatement)
        .unwrap();
    assert_eq!(
        children(&operation),
        [
            (BindingHeader, "our log: ('a, 'b) -> ()".into()),
            (Newline, "\n".into()),
            (Whitespace, "        ".into()),
            (WhereClause, "where 'a: Show".into()),
            (Newline, "\n".into()),
            (Whitespace, "        ".into()),
            (WhereClause, "where 'b: Display".into()),
        ]
    );
    let clauses = operation
        .children()
        .filter(|n| n.kind() == WhereClause)
        .collect::<Vec<_>>();
    assert_clause(&clauses[0], "'a", "Show");
    assert_clause(&clauses[1], "'b", "Display");
    let binding = clean("my f(x: 'a, y: 'b) =\n    where 'a: Show\n    where 'b: Display\n    x\n");
    let binding_clauses = binding
        .descendants()
        .filter(|n| n.kind() == WhereClause)
        .collect::<Vec<_>>();
    assert_eq!(binding_clauses.len(), 2);
    for (actual, control) in clauses.iter().zip(binding_clauses) {
        assert_eq!(children(actual), children(&control));
        assert_eq!(control.parent().unwrap().kind(), IndentedStatementBlock);
    }
}

#[test]
fn operation_where_preserves_leading_and_attached_member_docs() {
    use SyntaxKind::*;
    let source = "act a:\n    -- leading\n    our log: 'b -> () -- trailing\n        where 'b: Display\n    -- next\n    our other: () -> ()\n";
    let root = clean(source);
    let operation = root
        .descendants()
        .find(|n| n.kind() == BindingStatement)
        .unwrap();
    let clause = operation.last_child().unwrap();
    assert_clause(&clause, "'b", "Display");
    let trailing = operation
        .children()
        .find(|n| n.kind() == DocCommentDeclaration)
        .unwrap();
    assert_eq!(trailing.to_string(), "-- trailing");
    assert_eq!(trailing.parent(), Some(operation.clone()));
    assert_eq!(
        root.descendants()
            .filter(|n| n.kind() == DocCommentDeclaration)
            .map(|n| (n.to_string(), n.parent().unwrap().kind()))
            .collect::<Vec<_>>(),
        [
            ("-- leading".into(), Statement),
            ("-- trailing".into(), BindingStatement),
            ("-- next".into(), Statement),
        ]
    );
    assert_eq!(
        root.descendants()
            .filter(|n| n.kind() == BindingStatement)
            .count(),
        2
    );
}

#[test]
fn operation_where_uses_the_same_admission_in_braced_and_inline_act_bodies() {
    use SyntaxKind::*;
    for source in [
        "act a {\n    pub log: 'b -> ()\n        where 'b: Display\n    pub other: () -> ()\n}\n",
        "act a: our log: 'b -> ()\n    where 'b: Display\n",
        "act a:\r\n    our log: 'b -> ()\r\n        where 'b: Display\r\n",
    ] {
        let root = clean(source);
        let clauses = root
            .descendants()
            .filter(|n| n.kind() == WhereClause)
            .collect::<Vec<_>>();
        assert_eq!(clauses.len(), 1);
        assert_clause(&clauses[0], "'b", "Display");
    }
}

#[test]
fn operation_without_where_and_nested_block_where_keep_their_owners() {
    use SyntaxKind::*;
    let root = clean("act a:\n    our log: 'b -> ()\n");
    let operation = root
        .descendants()
        .find(|n| n.kind() == BindingStatement)
        .unwrap();
    assert_eq!(
        children(&operation),
        [(BindingHeader, "our log: 'b -> ()".into())]
    );
    for source in [
        "my f = if true:\n    where 'a: Display\n    1\n",
        "act a:\n    my f = if true:\n        where 'a: Display\n        1\n",
    ] {
        let root = clean(source);
        assert!(!root.descendants().any(|n| n.kind() == WhereClause));
        let chain = root
            .descendants()
            .find(|n| n.kind() == OperatorChain && n.to_string().starts_with("where"))
            .unwrap();
        assert_eq!(
            chain.children().map(|n| n.kind()).collect::<Vec<_>>(),
            [IdentifierExpression, MlArgument, ColonApplicationTail]
        );
    }
}

#[test]
fn same_line_where_keeps_binding_expression_and_signature_recovery_behavior() {
    use SyntaxKind::*;
    let binding = clean("my f(x: 'b) = where 'b: Display\n");
    assert!(!binding.descendants().any(|n| n.kind() == WhereClause));
    for source in [
        "my f: 'b -> () where 'b: Display\n",
        "act a:\n    our log: 'b -> () where 'b: Display\n",
    ] {
        let parsed = parse(source);
        let root = SyntaxNode::new_root(parsed.green().clone());
        assert!(!root.descendants().any(|n| n.kind() == WhereClause));
        let recoveries = parsed.structural_recoveries();
        assert_eq!(recoveries.len(), 1);
        assert_eq!(
            recoveries[0].kind(),
            crate::StructuralRecoveryKind::RawError
        );
        assert_eq!(&source[recoveries[0].range().clone()], ": Display");
    }
}

#[test]
fn bodyless_act_binding_without_a_signature_does_not_admit_where_after_its_doc() {
    for source in [
        "act a:\n    our log -- trailing\n        where 'b: Display\n",
        "act a {\n    our log -- trailing\n        where 'b: Display\n}\n",
    ] {
        let parsed = parse(source);
        let root = SyntaxNode::new_root(parsed.green().clone());
        assert!(
            !root
                .descendants()
                .any(|n| n.kind() == SyntaxKind::WhereClause)
        );
        let member = root
            .descendants()
            .find(|n| n.kind() == SyntaxKind::BindingStatement)
            .unwrap();
        assert_eq!(member.first_child().unwrap().to_string(), "our log");
        assert_eq!(
            member.last_child().unwrap().kind(),
            SyntaxKind::DocCommentDeclaration
        );
    }
}

#[test]
fn role_method_signature_where_keeps_its_pre_wp17_recovery_cst() {
    // Recorded before WP-17 with syntax_guide_check --tree. Role methods are
    // outside WP-17: where remains type application, followed by root recovery.
    let source = "role a 'x:\n    our log: 'b -> ()\n        where 'b: Display\n";
    let parsed = parse(source);
    let root = SyntaxNode::new_root(parsed.green().clone());
    assert_eq!(
        format!("{root:#?}"),
        r#"Root@0..59
  RoleDeclaration@0..49
    RoleKw@0..4 "role"
    Whitespace@4..5 " "
    TypeExpression@5..9
      Identifier@5..6 "a"
      TypeApplyArgument@6..9
        Whitespace@6..7 " "
        TypeExpression@7..9
          SigilIdentifier@7..9 "'x"
    Colon@9..10 ":"
    IndentedStatementBlock@10..49
      Newline@10..11 "\n"
      Whitespace@11..15 "    "
      Statement@15..49
        BindingStatement@15..49
          BindingHeader@15..49
            OurKw@15..18 "our"
            Whitespace@18..19 " "
            Pattern@19..49
              IdentifierPattern@19..22
                Identifier@19..22 "log"
              PatternTypeAnnotation@22..49
                Colon@22..23 ":"
                Whitespace@23..24 " "
                TypeExpression@24..49
                  SigilIdentifier@24..26 "'b"
                  TypeArrowTail@26..49
                    Whitespace@26..27 " "
                    Arrow@27..29 "->"
                    TypeExpression@29..49
                      ParenthesizedTypeGroup@29..32
                        Whitespace@29..30 " "
                        LParen@30..31 "("
                        RParen@31..32 ")"
                      TypeApplyArgument@32..46
                        Newline@32..33 "\n"
                        Whitespace@33..41 "        "
                        TypeExpression@41..46
                          Identifier@41..46 "where"
                      TypeApplyArgument@46..49
                        Whitespace@46..47 " "
                        TypeExpression@47..49
                          SigilIdentifier@47..49 "'b"
  Error@49..50 ":"
  Error@50..51 " "
  Error@51..58 "Display"
  Newline@58..59 "\n"
"#
    );
    assert!(
        !root
            .descendants()
            .any(|n| n.kind() == SyntaxKind::WhereClause)
    );
    assert_eq!(parsed.structural_recoveries().len(), 1);
    assert_eq!(parsed.structural_recoveries()[0].range(), &(49..58));
}
