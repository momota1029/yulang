use super::*;

#[test]
fn catch_with_target_keeps_exact_cst_for_all_block_variants() {
    // Captured before WP-16: inline, indented and direct braced blocks
    // retain their exact CST when the target is present.
    for (source, expected) in [
        (
            "catch a: v -> v\n",
            r#"Root@0..16
  OperatorChain@0..15
    CatchExpression@0..15
      CatchKw@0..5 "catch"
      CatchScrutinee@5..7
        OperatorChain@5..7
          IdentifierExpression@5..7
            Whitespace@5..6 " "
            Identifier@6..7 "a"
      CatchBlock@7..15
        Colon@7..8 ":"
        Whitespace@8..9 " "
        CatchArm@9..15
          Pattern@9..10
            IdentifierPattern@9..10
              Identifier@9..10 "v"
          Whitespace@10..11 " "
          Arrow@11..13 "->"
          Whitespace@13..14 " "
          OperatorChain@14..15
            IdentifierExpression@14..15
              Identifier@14..15 "v"
  Newline@15..16 "\n"
"#,
        ),
        (
            "catch a:\n    v -> v\n",
            r#"Root@0..20
  OperatorChain@0..19
    CatchExpression@0..19
      CatchKw@0..5 "catch"
      CatchScrutinee@5..7
        OperatorChain@5..7
          IdentifierExpression@5..7
            Whitespace@5..6 " "
            Identifier@6..7 "a"
      CatchBlock@7..19
        Colon@7..8 ":"
        Newline@8..9 "\n"
        Whitespace@9..13 "    "
        CatchArm@13..19
          Pattern@13..14
            IdentifierPattern@13..14
              Identifier@13..14 "v"
          Whitespace@14..15 " "
          Arrow@15..17 "->"
          Whitespace@17..18 " "
          OperatorChain@18..19
            IdentifierExpression@18..19
              Identifier@18..19 "v"
  Newline@19..20 "\n"
"#,
        ),
        (
            "catch a { v -> v }\n",
            r#"Root@0..19
  OperatorChain@0..18
    CatchExpression@0..18
      CatchKw@0..5 "catch"
      CatchScrutinee@5..7
        OperatorChain@5..7
          IdentifierExpression@5..7
            Whitespace@5..6 " "
            Identifier@6..7 "a"
      CatchBlock@7..18
        Whitespace@7..8 " "
        LBrace@8..9 "{"
        Whitespace@9..10 " "
        CatchArm@10..16
          Pattern@10..11
            IdentifierPattern@10..11
              Identifier@10..11 "v"
          Whitespace@11..12 " "
          Arrow@12..14 "->"
          Whitespace@14..15 " "
          OperatorChain@15..16
            IdentifierExpression@15..16
              Identifier@15..16 "v"
        Whitespace@16..17 " "
        RBrace@17..18 "}"
  Newline@18..19 "\n"
"#,
        ),
    ] {
        let root = case_like_literal_production(source);
        assert_eq!(format!("{root:#?}"), expected, "{source:?}");
    }
}

#[test]
fn catch_head_without_same_line_colon_keeps_exact_recovery_cst() {
    // Captured before WP-16: missing targets without a same-line colon
    // retain their exact CST, including cross-line colons and direct braces.
    for (source, expected) in [
        (
            "catch",
            r#"Root@0..5
  OperatorChain@0..5
    CatchExpression@0..5
      CatchKw@0..5 "catch"
      CatchScrutinee@5..5
        OperatorChain@5..5
          Missing@5..5
      CatchBlock@5..5
        Missing@5..5
"#,
        ),
        (
            "catch\n",
            r#"Root@0..6
  OperatorChain@0..6
    CatchExpression@0..6
      CatchKw@0..5 "catch"
      CatchScrutinee@5..6
        OperatorChain@5..6
          Newline@5..6 "\n"
          Missing@6..6
      CatchBlock@6..6
        Missing@6..6
"#,
        ),
        (
            "catch\n    v -> v\n",
            r#"Root@0..17
  OperatorChain@0..12
    CatchExpression@0..12
      CatchKw@0..5 "catch"
      CatchScrutinee@5..11
        OperatorChain@5..11
          IdentifierExpression@5..11
            Newline@5..6 "\n"
            Whitespace@6..10 "    "
            Identifier@10..11 "v"
      CatchBlock@11..12
        Whitespace@11..12 " "
        Missing@12..12
  Error@12..13 "-"
  Error@13..14 ">"
  Error@14..15 " "
  Error@15..16 "v"
  Newline@16..17 "\n"
"#,
        ),
        (
            "catch\n    : v -> v\n",
            r#"Root@0..19
  OperatorChain@0..18
    CatchExpression@0..18
      CatchKw@0..5 "catch"
      CatchScrutinee@5..5
        OperatorChain@5..5
          Missing@5..5
      CatchBlock@5..18
        Newline@5..6 "\n"
        Whitespace@6..10 "    "
        Colon@10..11 ":"
        Whitespace@11..12 " "
        CatchArm@12..18
          Pattern@12..13
            IdentifierPattern@12..13
              Identifier@12..13 "v"
          Whitespace@13..14 " "
          Arrow@14..16 "->"
          Whitespace@16..17 " "
          OperatorChain@17..18
            IdentifierExpression@17..18
              Identifier@17..18 "v"
  Newline@18..19 "\n"
"#,
        ),
        (
            "catch { v -> v }\n",
            r#"Root@0..17
  OperatorChain@0..16
    CatchExpression@0..16
      CatchKw@0..5 "catch"
      CatchScrutinee@5..5
        OperatorChain@5..5
          Missing@5..5
      CatchBlock@5..16
        Whitespace@5..6 " "
        LBrace@6..7 "{"
        Whitespace@7..8 " "
        CatchArm@8..14
          Pattern@8..9
            IdentifierPattern@8..9
              Identifier@8..9 "v"
          Whitespace@9..10 " "
          Arrow@10..12 "->"
          Whitespace@12..13 " "
          OperatorChain@13..14
            IdentifierExpression@13..14
              Identifier@13..14 "v"
        Whitespace@14..15 " "
        RBrace@15..16 "}"
  Newline@16..17 "\n"
"#,
        ),
    ] {
        let text: std::sync::Arc<crate::SourceText> = std::sync::Arc::from(source);
        let parsed = crate::parse_file(
            text.clone(),
            std::sync::Arc::new(crate::scan_header(text)),
            std::sync::Arc::new(crate::SyntaxEnvironment::empty()),
        );
        assert_eq!(parsed.green().to_string(), source);
        assert!(!parsed.structural_recoveries().is_empty(), "{source:?}");
        let root = SyntaxNode::new_root(parsed.green().clone());
        assert_eq!(format!("{root:#?}"), expected, "{source:?}");
    }
}

#[test]
fn catch_without_target_has_exact_inline_and_indented_cst() {
    // WP-16 supersedes the two catch rows formerly in
    // case_head_unchanged_recovery_fixtures: the same CatchBlock remains,
    // but the absent target no longer creates CatchScrutinee(Missing).
    for (source, expected) in [
        (
            "catch:\n    0 -> 1\n",
            r#"Root@0..18
  OperatorChain@0..17
    CatchExpression@0..17
      CatchKw@0..5 "catch"
      CatchBlock@5..17
        Colon@5..6 ":"
        Newline@6..7 "\n"
        Whitespace@7..11 "    "
        CatchArm@11..17
          Pattern@11..12
            IntegerPattern@11..12
              Integer@11..12 "0"
          Whitespace@12..13 " "
          Arrow@13..15 "->"
          Whitespace@15..16 " "
          OperatorChain@16..17
            IntegerLiteral@16..17
              Integer@16..17 "1"
  Newline@17..18 "\n"
"#,
        ),
        (
            "catch: 0 -> 1\n",
            r#"Root@0..14
  OperatorChain@0..13
    CatchExpression@0..13
      CatchKw@0..5 "catch"
      CatchBlock@5..13
        Colon@5..6 ":"
        Whitespace@6..7 " "
        CatchArm@7..13
          Pattern@7..8
            IntegerPattern@7..8
              Integer@7..8 "0"
          Whitespace@8..9 " "
          Arrow@9..11 "->"
          Whitespace@11..12 " "
          OperatorChain@12..13
            IntegerLiteral@12..13
              Integer@12..13 "1"
  Newline@13..14 "\n"
"#,
        ),
    ] {
        let root = case_like_literal_production(source);
        assert_eq!(format!("{root:#?}"), expected, "{source:?}");
    }
}

#[test]
fn catch_without_target_composes_in_expression_contexts() {
    for (source, ancestor_kind, expected_arm_counts) in [
        (
            "my h = catch:\n    flip::coin(), k -> k true\n    v -> v",
            SyntaxKind::BindingBody,
            vec![2],
        ),
        (
            "my h=catch:\n    flip::coin(), k -> k true\n    v -> v",
            SyntaxKind::BindingBody,
            vec![2],
        ),
        (
            "infix (|) 1 2 = pipe\nx | catch:\n    flip::coin(), k -> k true\n    v -> v",
            SyntaxKind::OperatorChain,
            vec![2],
        ),
        (
            "apply (catch:\n    flip::coin(), k -> k true\n    v -> v\n)",
            SyntaxKind::MlArgument,
            vec![2],
        ),
        ("apply(catch: v -> v)", SyntaxKind::CallTail, vec![1]),
        (
            "case n:\n    0 -> catch:\n        flip::coin(), k -> k true\n        v -> v\n    _ -> fallback",
            SyntaxKind::CaseArm,
            vec![2],
        ),
        (
            "catch a:\n    0 -> catch:\n        flip::coin(), k -> k true\n        v -> v\n    _ -> fallback",
            SyntaxKind::CatchArm,
            vec![2],
        ),
        (
            "catch a { v -> catch: v -> v, _ -> fallback }",
            SyntaxKind::CatchArm,
            vec![1],
        ),
        (
            "catch:\n    0 -> catch:\n        v -> v\n    _ -> fallback",
            SyntaxKind::Root,
            vec![2, 1],
        ),
    ] {
        let root = case_like_literal_production(source);
        let catches = root
            .descendants()
            .filter(|node| node.kind() == SyntaxKind::CatchExpression)
            .filter(|node| {
                !node
                    .children()
                    .any(|child| child.kind() == SyntaxKind::CatchScrutinee)
            })
            .collect::<Vec<_>>();
        assert_eq!(catches.len(), expected_arm_counts.len(), "{source:?}");
        for (catch, expected_arms) in catches.iter().zip(expected_arm_counts) {
            assert_eq!(
                catch
                    .children_with_tokens()
                    .map(|child| child.kind())
                    .collect::<Vec<_>>(),
                [SyntaxKind::CatchKw, SyntaxKind::CatchBlock],
                "{source:?}"
            );
            let block = catch.first_child().expect("CatchBlock");
            assert_eq!(
                block
                    .children()
                    .filter(|child| child.kind() == SyntaxKind::CatchArm)
                    .count(),
                expected_arms,
                "{source:?}"
            );
            assert!(
                catch
                    .ancestors()
                    .skip(1)
                    .any(|node| node.kind() == ancestor_kind),
                "{source:?}"
            );
        }
    }
}

#[test]
fn catch_without_target_admits_same_line_trivia_and_adjacent_arm_patterns() {
    let operators = OperatorTable::from_declarations([OperatorDeclaration::new(
        "catch",
        OperatorFixities::new().with_prefix(BindingPower::scalar(40)),
    )])
    .expect("contextual catch keyword wins over a dynamic operator");
    for source in [
        "catch: v -> v",
        "catch \t: v -> v",
        "catch /* arms */ : v -> v",
        "catch:v -> v",
        "catch /* arms */ :v -> v",
        "catch:flip::coin(), k -> k true",
    ] {
        let root = case_like_literal_production(source);
        assert!(
            !root
                .descendants()
                .any(|node| node.kind() == SyntaxKind::CatchScrutinee),
            "{source:?}"
        );
        let (green, _) = run_with(source, &operators);
        assert_eq!(green.to_string(), source);
        assert!(structural_facts(&green).is_empty(), "{source:?}");
        let root = SyntaxNode::new_root(green);
        assert_eq!(
            root.descendants()
                .filter(|node| node.kind() == SyntaxKind::CatchExpression)
                .count(),
            1,
            "{source:?}"
        );
        assert!(
            !root
                .descendants()
                .any(|node| node.kind() == SyntaxKind::CatchScrutinee),
            "{source:?}"
        );
    }
}

#[test]
fn catch_without_target_keeps_continuation_pattern_and_body_slots() {
    use SyntaxKind::*;
    for source in [
        "catch a: flip::coin(), k -> k true",
        "catch a { flip::coin(), k -> k true }",
        "catch: flip::coin(), k -> k true",
        "catch:\n    flip::coin(), k -> k true\n    v -> v",
    ] {
        let root = case_like_literal_production(source);
        let arm = expression(&root, CatchArm);
        assert_eq!(
            case_schema_children(&arm),
            [Pattern, Comma, Pattern, Arrow, OperatorChain],
            "{source:?}"
        );
        let patterns = arm
            .children()
            .filter(|node| node.kind() == Pattern)
            .collect::<Vec<_>>();
        assert_eq!(patterns[0].to_string(), "flip::coin()");
        // The existing handler Pattern owns its leading trivia, unlike the
        // first arm Pattern; omitting the catch target keeps that ownership.
        assert_eq!(patterns[1].to_string(), " k");
        let body = arm.last_child().unwrap();
        assert_eq!(body.to_string(), "k true");
        assert_eq!(
            case_schema_children(&body),
            [IdentifierExpression, MlArgument]
        );
    }
}
