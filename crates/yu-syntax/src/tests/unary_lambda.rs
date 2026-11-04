use std::sync::Arc;

use crate::tests::support::*;

fn production(source: &str) -> SyntaxNode {
    let source: Arc<crate::SourceText> = Arc::from(source);
    let parsed = crate::parse_file(
        Arc::clone(&source),
        Arc::new(crate::scan_header(Arc::clone(&source))),
        Arc::new(crate::SyntaxEnvironment::empty()),
    );
    assert_eq!(parsed.green().to_string(), source.as_ref());
    let root = SyntaxNode::new_root(parsed.green().clone());
    for token in root
        .descendants_with_tokens()
        .filter_map(|element| element.into_token())
    {
        let range = usize::from(token.text_range().start())..usize::from(token.text_range().end());
        assert_eq!(&source[range], token.text());
    }
    root
}

fn lambdas(root: &SyntaxNode) -> Vec<SyntaxNode> {
    root.descendants()
        .filter(|node| node.kind() == SyntaxKind::LambdaExpression)
        .collect()
}

fn assert_clean(root: &SyntaxNode) {
    assert!(
        !root.descendants_with_tokens().any(|element| matches!(
            element.kind(),
            SyntaxKind::Error | SyntaxKind::Missing | SyntaxKind::Invalid
        )),
        "{root:#?}"
    );
}

#[test]
fn complete_headers_are_primaries_in_production_and_internal_entry() {
    for source in [
        r"\x -> x",
        // WP-10: superseded the unary-only admission pin (design memo WP-10).
        r"\x y -> x",
        r"g \i -> i",
        r"host (\x -> x)",
        r"host(\x -> x)",
        r"\x->g x",
        r"\x -> \y -> g x y",
        r"g \i -> if i: return i",
    ] {
        let root = production(source);
        assert_clean(&root);
        assert!(!lambdas(&root).is_empty(), "{source}");
        let (green, _) = run(source);
        assert_eq!(green.to_string(), source);
        assert_eq!(
            lambdas(&SyntaxNode::new_root(green)).len(),
            lambdas(&root).len()
        );
    }
    let root = production(r"f \x -> g x");
    let lambda = lambdas(&root).remove(0);
    let body = lambda
        .children()
        .find(|node| node.kind() == SyntaxKind::OperatorChain)
        .unwrap();
    assert!(
        body.descendants()
            .any(|node| node.kind() == SyntaxKind::MlArgument)
    );
    assert_eq!(body.to_string(), " g x");
    assert!(
        lambda
            .ancestors()
            .any(|node| node.kind() == SyntaxKind::MlArgument)
    );
}

#[test]
fn multiple_identifier_and_parenthesized_pattern_parameters_parse_cleanly() {
    for source in [
        r"\x y z -> x",
        r"\(a, b) -> a",
        r"\x (a, b) -> a",
        r"\(a, b) (c, d) -> a",
        r"\(just x) -> x",
        r"\(just x) y -> x",
        r"\(x: int) -> x",
        r"\_ -> 0",
        r"f (\x y -> x)",
        r"f \x y -> x",
        r"\x -> \y -> x",
        "\\x y -> if x:\n  y",
    ] {
        let root = production(source);
        assert_clean(&root);
        assert!(!lambdas(&root).is_empty(), "{source}: {root:#?}");
    }
}

#[test]
fn bare_reference_patterns_are_clean_lambda_parameters() {
    let sources = [
        r"my x = \&a -> 1",
        r"my x = \&a &b -> 1",
        "infix (+) 40 41 = 0\nmy x = \\&a ->\n    &a = $a + 1\n    $a",
        r"my x = &a::run 0 (\&a -> $a)",
        r"\x &a y -> 1",
    ];
    for source in sources {
        let source_text: Arc<crate::SourceText> = Arc::from(source);
        let parsed = crate::parse_file(
            Arc::clone(&source_text),
            Arc::new(crate::scan_header(Arc::clone(&source_text))),
            Arc::new(crate::SyntaxEnvironment::empty()),
        );
        assert!(parsed.structural_recoveries().is_empty(), "{source}");
        assert!(parsed.syntax_diagnostics().unwrap().is_empty(), "{source}");
        let root = production(source);
        assert_clean(&root);
        assert_eq!(root.to_string(), source);
        assert_eq!(lambdas(&root).len(), 1, "{source}: {root:#?}");
    }

    let source = "my incr &r = 1\nmy f = \\&a -> 1";
    let root = production(source);
    let binding_reference_parameter = root
        .descendants()
        .filter(|node| node.kind() == SyntaxKind::Pattern)
        .find(|node| {
            node.descendants_with_tokens().any(|element| {
                element.kind() == SyntaxKind::SigilIdentifier && element.to_string() == "&r"
            })
        })
        .expect("binding reference parameter Pattern");
    let lambda_reference_parameter = lambdas(&root)
        .remove(0)
        .children()
        .find(|node| node.kind() == SyntaxKind::Pattern)
        .expect("lambda reference parameter Pattern");
    assert_eq!(
        lambda_reference_parameter.kind(),
        binding_reference_parameter.kind()
    );
    assert_eq!(
        lambda_reference_parameter.first_child().unwrap().kind(),
        binding_reference_parameter.first_child().unwrap().kind()
    );
}

#[test]
fn lambda_parameters_keep_the_direct_cst_shape() {
    let unary = lambdas(&production(r"\x -> x")).remove(0);
    assert_eq!(
        unary
            .children_with_tokens()
            .map(|element| element.kind())
            .collect::<Vec<_>>(),
        [
            SyntaxKind::Backslash,
            SyntaxKind::Identifier,
            SyntaxKind::Whitespace,
            SyntaxKind::Arrow,
            SyntaxKind::OperatorChain,
        ]
    );

    let lambda = lambdas(&production(r"\x (a, b) y -> a")).remove(0);
    assert_eq!(
        lambda
            .children_with_tokens()
            .filter(|element| !matches!(element.kind(), SyntaxKind::Whitespace))
            .map(|element| element.kind())
            .collect::<Vec<_>>(),
        [
            SyntaxKind::Backslash,
            SyntaxKind::Identifier,
            SyntaxKind::Pattern,
            SyntaxKind::Identifier,
            SyntaxKind::Arrow,
            SyntaxKind::OperatorChain,
        ]
    );
    let parameter = lambda
        .children()
        .find(|node| node.kind() == SyntaxKind::Pattern)
        .expect("parenthesized parameter Pattern");
    assert_eq!(parameter.to_string(), "(a, b)");
    assert!(
        parameter
            .children()
            .any(|node| node.kind() == SyntaxKind::ParenthesizedPattern)
    );
}

#[test]
fn parenthesized_header_lookahead_ignores_nested_and_opaque_parentheses() {
    for source in [
        r"\((a, b)) -> a",
        r#"\(")") -> 0"#,
        r#"\(~")") -> 0"#,
        r"\(/* outer /* ) */ still */ x) -> x",
        "\\(x, // )\n  y) -> x",
    ] {
        let root = production(source);
        assert_clean(&root);
        assert_eq!(lambdas(&root).len(), 1, "{source}: {root:#?}");
    }
}

#[test]
fn header_uses_maximal_raw_identifier_and_logical_inline_trivia() {
    for binder in ["_", "値", "café?", "ready!", "if", "case", "catch", "rule"] {
        let source = format!("\\ /*one\n two*/ {binder} /*three*/ -> {binder}");
        let root = production(&source);
        let lambda = lambdas(&root).remove(0);
        let token = lambda
            .children_with_tokens()
            .filter_map(|element| element.into_token())
            .find(|token| token.kind() == SyntaxKind::Identifier)
            .unwrap();
        assert_eq!(token.text(), binder);
        let range = usize::from(token.text_range().start())..usize::from(token.text_range().end());
        assert_eq!(&source[range], binder);
        // Contextual words in the body keep their ordinary expression grammar.
        if !["if", "case", "catch"].contains(&binder) {
            assert_clean(&root);
        }
    }
}

#[test]
fn nonmatching_headers_do_not_create_lambda_nodes() {
    for source in [
        r"\",
        r"\x",
        r"\x -",
        r"\x - > x",
        r"\ ->",
        r"\x y",
        r"\(a, b -> a",
        r"\1 -> x",
        r"\x.y -> x",
        r"\x ->> x",
        "\\\nx -> x",
        "\\x\n-> x",
        "\\ //c\nx -> x",
    ] {
        assert!(lambdas(&production(source)).is_empty(), "{source}");
    }
}

#[test]
fn adjacent_parenthesized_groups_follow_pattern_call_adjacency() {
    let root = production(r"\(a, b)(c) -> a");
    assert_clean(&root);
    let lambda = lambdas(&root).remove(0);
    let parameters = lambda
        .children()
        .filter(|node| node.kind() == SyntaxKind::Pattern)
        .collect::<Vec<_>>();
    assert_eq!(parameters.len(), 1);
    assert!(
        parameters[0]
            .descendants()
            .any(|node| node.kind() == SyntaxKind::PatternCallTail)
    );
}

#[test]
fn malformed_parenthesized_parameters_keep_pattern_recovery() {
    let trailing_comma = production(r"\(a,) -> a");
    assert_clean(&trailing_comma);
    assert_eq!(lambdas(&trailing_comma).len(), 1);

    let root = production(r"\(,) x -> x");
    let lambda = lambdas(&root).remove(0);
    assert!(
        lambda
            .children()
            .any(|node| node.kind() == SyntaxKind::Pattern)
    );
    assert!(
        lambda
            .children_with_tokens()
            .any(|element| element.kind() == SyntaxKind::Arrow)
    );
    assert!(
        lambda
            .descendants_with_tokens()
            .any(|element| matches!(element.kind(), SyntaxKind::Missing | SyntaxKind::Error)),
        "{lambda:#?}"
    );
}

#[test]
fn doubled_backslash_keeps_root_error_recovery() {
    let root = production(r"\\x -> x");
    // A failed header retains ordinary single-character Error ownership.
    let error = root
        .descendants_with_tokens()
        .filter_map(|element| element.into_token())
        .find(|token| token.kind() == SyntaxKind::Error)
        .unwrap();
    assert_eq!(error.text(), "\\");
    assert_eq!(usize::from(error.text_range().start()), 0);
    assert_eq!(usize::from(error.text_range().end()), 1);
    // Ordinary root malformed-run recovery consumes the remaining same-line Items.
    assert!(lambdas(&root).is_empty());
}

#[test]
fn complete_headers_precede_dynamic_backslash_at_both_sites() {
    for fixities in [
        OperatorFixities::new().with_prefix(BindingPower::scalar(70)),
        OperatorFixities::new().with_suffix(BindingPower::scalar(70)),
        OperatorFixities::new().with_infix(BindingPower::scalar(70), BindingPower::scalar(71)),
    ] {
        let table =
            OperatorTable::from_declarations([OperatorDeclaration::new("\\", fixities)]).unwrap();
        for source in [r"\x -> x", r"\x y -> x", r"g \i -> g i"] {
            let (green, _) = run_with(source, &table);
            assert_eq!(green.to_string(), source);
            let root = SyntaxNode::new_root(green);
            assert_clean(&root);
            assert_eq!(lambdas(&root).len(), 1);
            assert!(!root.descendants().any(|node| matches!(
                node.kind(),
                SyntaxKind::PrefixOperatorUse
                    | SyntaxKind::InfixOperatorUse
                    | SyntaxKind::SuffixOperatorUse
            )));
        }
    }
    let table = OperatorTable::from_declarations([OperatorDeclaration::new(
        "\\",
        OperatorFixities::new().with_prefix(BindingPower::scalar(70)),
    )])
    .unwrap();
    let (green, _) = run_with(r"\x", &table);
    assert!(
        SyntaxNode::new_root(green)
            .descendants()
            .any(|node| node.kind() == SyntaxKind::PrefixOperatorUse)
    );
    let (green, _) = run_with(r"\x y", &table);
    let root = SyntaxNode::new_root(green);
    assert!(lambdas(&root).is_empty());
    assert!(
        root.descendants()
            .any(|node| node.kind() == SyntaxKind::PrefixOperatorUse)
    );

    let table = OperatorTable::from_declarations([OperatorDeclaration::new(
        "\\",
        OperatorFixities::new().with_infix(BindingPower::scalar(40), BindingPower::scalar(41)),
    )])
    .unwrap();
    let (green, _) = run_with(r"left \ right", &table);
    let root = SyntaxNode::new_root(green);
    assert!(lambdas(&root).is_empty());
    assert!(
        root.descendants()
            .any(|node| node.kind() == SyntaxKind::InfixOperatorUse)
    );
}

#[test]
fn committed_header_survives_missing_invalid_and_caller_boundaries() {
    for source in [
        r"\x ->",
        r"\x -> @",
        "\\x ->\nnext",
        "\\x -> @\nnext",
        r"f(\x ->, next)",
        r"f(\x ->)",
        r"f(\x -> @, next)",
        "f(\\x ->\nnext)",
    ] {
        let root = production(source);
        let lambda = lambdas(&root).remove(0);
        assert!(
            lambda
                .children_with_tokens()
                .any(|element| element.kind() == SyntaxKind::Identifier)
        );
        assert!(
            lambda
                .children_with_tokens()
                .any(|element| element.kind() == SyntaxKind::Arrow)
        );
        assert!(
            lambda
                .descendants_with_tokens()
                .any(|element| matches!(element.kind(), SyntaxKind::Missing | SyntaxKind::Error)),
            "{source}"
        );
        assert!(
            !lambda.to_string().contains("next"),
            "{source}: {lambda:#?}"
        );
    }
}

#[test]
fn malformed_operator_operand_returns_separating_newline_after_committed_header() {
    let operators = dynamic_operator_table();
    for body in ["y + @", "~ @"] {
        for (open, close) in [("", ""), ("f(", ")")] {
            let source = format!("{open}\\x -> {body}\nnext{close}");
            let root = SyntaxNode::new_root(crate::cursor::parse_root(&source, &operators));
            assert_eq!(root.to_string(), source);
            let lambda = lambdas(&root).remove(0);
            assert!(
                lambda
                    .children_with_tokens()
                    .any(|element| element.kind() == SyntaxKind::Identifier
                        && element.to_string() == "x")
            );
            assert!(
                lambda
                    .children_with_tokens()
                    .any(|element| element.kind() == SyntaxKind::Arrow)
            );
            assert!(
                lambda
                    .descendants_with_tokens()
                    .any(|element| element.kind() == SyntaxKind::Error
                        && element.to_string().contains('@'))
            );
            assert_eq!(lambda.to_string(), format!("\\x -> {body}"), "{source}");
            let next = root
                .descendants_with_tokens()
                .filter_map(|element| element.into_token())
                .find(|token| token.text() == "next")
                .expect("next remains outside lambda");
            assert!(
                !next.parent_ancestors().any(|node| node == lambda),
                "{source}"
            );
        }
    }
}

#[test]
fn malformed_operator_operand_retries_same_line_and_deeper_continuations() {
    let operators = dynamic_operator_table();
    for body in ["y + @", "~ @"] {
        for gap in [" ", "\n  ", "\r\n  "] {
            for (open, close) in [("", ""), ("f(", ")")] {
                let source = format!("{open}\\x -> {body}{gap}next{close}");
                let root = SyntaxNode::new_root(crate::cursor::parse_root(&source, &operators));
                assert_eq!(root.to_string(), source);
                let lambda = lambdas(&root).remove(0);
                assert_eq!(
                    lambda.to_string(),
                    format!("\\x -> {body}{gap}next"),
                    "{source}"
                );
                assert!(
                    lambda
                        .descendants_with_tokens()
                        .any(|element| element.kind() == SyntaxKind::Error
                            && element.to_string().contains('@'))
                );
                assert!(
                    lambda
                        .descendants_with_tokens()
                        .any(|element| element.kind() == SyntaxKind::Identifier
                            && element.to_string() == "next")
                );
            }
        }
    }
}

#[test]
fn body_and_header_return_fences_without_crossing_them() {
    use crate::lexical::yumark::{FenceOpener, FencePrefixPolicy};
    let fence = FenceBoundary {
        opener: FenceOpener {
            line: 0,
            marker: 0..3,
            marker_width: 3,
        },
        prefix_policy: FencePrefixPolicy::None,
        close_column: 0,
    };
    for source in [
        "\\x ->\n```\nouter",
        "\\x -> @\n```\nouter",
        "\\x -> x\n```\nouter",
    ] {
        let (green, exit, remainder) = run_normalized(
            source,
            &OperatorTable::empty(),
            0,
            LineEntry::InLine,
            Some(&fence),
        );
        let root = SyntaxNode::new_root(green);
        assert_eq!(lambdas(&root).len(), 1);
        assert!(!root.to_string().contains("outer"));
        assert!(matches!(
            exit,
            Some(NormalizedExit::Complete(Err(Either::Left(_)), _))
        ));
        assert!(remainder.starts_with("```"), "{remainder:?}");
    }
    for source in ["\\ /*open\n```\nx -> x", "\\x /*open\n```\n-> x"] {
        let (green, _, remainder) = run_normalized(
            source,
            &OperatorTable::empty(),
            0,
            LineEntry::InLine,
            Some(&fence),
        );
        assert!(lambdas(&SyntaxNode::new_root(green)).is_empty());
        // Optional NUD rejection rolls the entire attempt back.
        assert_eq!(remainder, source);
    }
}

#[test]
fn binder_bypasses_registered_word_operator_selection() {
    let table = OperatorTable::from_declarations([OperatorDeclaration::new(
        "if",
        OperatorFixities::new().with_nullfix(),
    )])
    .unwrap();
    let (green, _) = run_with(r"g \if -> value", &table);
    let root = SyntaxNode::new_root(green);
    assert_clean(&root);
    let lambda = lambdas(&root).remove(0);
    assert!(
        lambda
            .children_with_tokens()
            .any(|element| element.kind() == SyntaxKind::Identifier && element.to_string() == "if")
    );
}

#[test]
fn callback_hygiene_expression_retains_the_full_lambda_body() {
    let source = r"g \i -> if i == 0: return i";
    let table = OperatorTable::from_declarations([OperatorDeclaration::new(
        "==",
        OperatorFixities::new().with_infix(BindingPower::scalar(40), BindingPower::scalar(41)),
    )])
    .unwrap();
    let root = SyntaxNode::new_root(crate::cursor::parse_root(source, &table));
    assert_eq!(root.to_string(), source);
    assert_clean(&root);
    let lambda = lambdas(&root).remove(0);
    assert_eq!(lambda.to_string(), r"\i -> if i == 0: return i");
    assert!(
        lambda
            .descendants()
            .any(|node| node.kind() == SyntaxKind::IfExpression)
    );
}

#[test]
fn recovery_capability_preserves_nested_rhs_and_if_sibling_boundaries() {
    let operators = dynamic_operator_table();
    for body in ["y + @", "~ @", "if", "if @", "if y", "if y + @"] {
        for newline in ["\n", "\r\n"] {
            for header in ["\\x -> ", "\\x -> \\y -> "] {
                let source = format!("{header}{body}{newline}next");
                let root = SyntaxNode::new_root(crate::cursor::parse_root(&source, &operators));
                assert_eq!(root.to_string(), source);
                for lambda in lambdas(&root) {
                    assert!(!lambda.to_string().contains(newline), "{source}: {root:#?}");
                }
                let next = root
                    .descendants_with_tokens()
                    .filter_map(|element| element.into_token())
                    .find(|token| token.kind() == SyntaxKind::Identifier && token.text() == "next")
                    .expect("next is admitted as an ordinary sibling identifier");
                assert!(
                    !next
                        .parent_ancestors()
                        .any(|node| node.kind() == SyntaxKind::LambdaExpression)
                );
                let (green, exit, _) =
                    run_normalized(&source, &operators, 0, LineEntry::InLine, None);
                assert_eq!(green.to_string(), format!("{header}{body}"));
                let Some(NormalizedExit::Complete(Err(Either::Left(item)), _)) = exit else {
                    panic!("the internal entry returns the unread sibling: {source}");
                };
                assert!(crate::lexical::observation::implicit_delimited_newline(
                    0,
                    item.leading_view()
                ));
            }
        }
    }
}

#[test]
fn lambda_recovery_activation_rebases_to_child_layout_and_returns_to_parent() {
    let operators = dynamic_operator_table();
    // Fresh children retain recovery activation at their local baseline; a
    // mandatory operand must return a local separator or dedent before retry.
    for child in ["(@\nvalue)", "{@\nvalue}", "if ok:\n  @\n  value"] {
        let source = format!("\\x -> {child} + @\nnext");
        let root = SyntaxNode::new_root(crate::cursor::parse_root(&source, &operators));
        assert_eq!(root.to_string(), source);
        let lambda = lambdas(&root).remove(0);
        assert!(lambda.to_string().contains("value"), "{source}: {root:#?}");
        assert!(!lambda.to_string().contains("next"), "{source}: {root:#?}");
        assert!(
            lambda
                .descendants_with_tokens()
                .filter_map(|element| element.into_token())
                .any(|token| token.kind() == SyntaxKind::Identifier && token.text() == "value")
        );
        assert!(
            lambda
                .descendants_with_tokens()
                .filter_map(|element| element.into_token())
                .any(|token| token.kind() == SyntaxKind::Error && token.text().contains('@'))
        );
    }
}

#[test]
fn case_label_admission_retains_the_lambda_caller_newline() {
    for newline in ["\n", "\r\n"] {
        let source = format!("\\x -> case{newline}'label");
        let (green, exit, _) =
            run_normalized(&source, &OperatorTable::empty(), 0, LineEntry::InLine, None);
        assert_eq!(green.to_string(), "\\x -> case");
        let Some(NormalizedExit::Complete(Err(Either::Left(item)), _)) = exit else {
            panic!("the label remains at the caller boundary");
        };
        assert!(crate::lexical::observation::implicit_delimited_newline(
            0,
            item.leading_view()
        ));
        assert_eq!(
            item.payload_view().token_kind(),
            Some(crate::lexical::item::TokenKind::SigilIdentifier)
        );
    }
}

#[test]
fn protected_structural_tokens_remain_pending_at_the_lambda_boundary() {
    use crate::lexical::item::TokenKind;
    for newline in ["\n", "\r\n"] {
        for (head, tail, kind) in [
            ("if", ": value", TokenKind::Colon),
            ("case", ": p -> value", TokenKind::Colon),
            ("catch", "{p -> value}", TokenKind::LBrace),
            ("case v: p if", "-> value", TokenKind::Arrow),
            ("case v: p", "if ok -> value", TokenKind::Identifier),
        ] {
            let prefix = format!("\\x -> {head}");
            let source = format!("{prefix}{newline}{tail}");
            let (green, exit, _) =
                run_normalized(&source, &OperatorTable::empty(), 0, LineEntry::InLine, None);
            assert_eq!(green.to_string(), prefix, "{source}");
            let Some(NormalizedExit::Complete(Err(Either::Left(item)), _)) = exit else {
                panic!("structural successor remains pending: {source}");
            };
            assert_eq!(item.payload_view().token_kind(), Some(kind), "{source}");
            assert!(crate::lexical::observation::implicit_delimited_newline(
                0,
                item.leading_view(),
            ));
            production(&source);
        }
    }
}

#[test]
fn ordinary_structural_punctuation_and_if_companions_keep_their_owner() {
    for body in [
        "if ok: value",
        "case v: p -> value",
        "catch v {p -> value}",
        "case v: p if ok -> value",
        "catch v: p, q -> value",
        "if ok:\n  value\nelse: other",
        "if ok:\n  value\nelsif other: result",
    ] {
        let source = format!("\\x -> {body}");
        let root = production(&source);
        assert_eq!(lambdas(&root).remove(0).to_string(), source);
        assert_clean(&root);
    }
}

#[test]
fn child_mandatory_operand_returns_dedent_before_recovery_retry() {
    let operators = dynamic_operator_table();
    for newline in ["\n", "\r\n"] {
        let child = format!("if ok:{newline}  @{newline}  value + @");
        let source = format!("\\x -> {child}{newline}next");
        let root = SyntaxNode::new_root(crate::cursor::parse_root(&source, &operators));
        assert_eq!(root.to_string(), source);
        let lambda = lambdas(&root).remove(0);
        assert!(lambda.to_string().contains("value"));
        assert!(!lambda.to_string().contains("next"), "{root:#?}");
        let next = root
            .descendants_with_tokens()
            .filter_map(|element| element.into_token())
            .find(|token| token.kind() == SyntaxKind::Identifier && token.text() == "next")
            .expect("dedented sibling remains an identifier");
        assert!(!next.parent_ancestors().any(|node| node == lambda));
    }
}

#[test]
fn unadmitted_dangling_operators_preserve_ordinary_pending_ownership() {
    let operators = dynamic_operator_table();
    // The operator scanner rejects a dangling follower at equal indentation;
    // no admitted mandatory operand exists for these two controls.
    for body in ["y +", "~"] {
        for newline in ["\n", "\r\n"] {
            let source = format!("\\x -> {body}{newline}next");
            let root = SyntaxNode::new_root(crate::cursor::parse_root(&source, &operators));
            assert_eq!(root.to_string(), source);
            let (green, exit, _remainder) =
                run_normalized(&source, &operators, 0, LineEntry::InLine, None);
            assert!(!green.to_string().contains("next"));
            let Some(NormalizedExit::Complete(Err(Either::Left(item)), _)) = exit else {
                panic!("ordinary pending Item remains: {source}");
            };
            let payload = item.payload_view();
            if body == "y +" {
                assert_eq!(green.to_string(), "\\x -> y");
                assert_eq!(payload.spelling(), Some("+"));
                assert_eq!(
                    payload.token_kind(),
                    Some(crate::lexical::item::TokenKind::Unknown)
                );
                assert!(payload.operator_use().is_none());
                assert!(!item.leading_view().has_ordinary_newline());
            } else {
                assert_eq!(green.to_string(), "\\x -> ~");
                assert_eq!(payload.spelling(), Some("next"));
                assert_eq!(
                    payload.token_kind(),
                    Some(crate::lexical::item::TokenKind::Identifier)
                );
                assert!(crate::lexical::observation::implicit_delimited_newline(
                    0,
                    item.leading_view(),
                ));
            }
        }
    }
}

#[test]
fn catch_handler_comma_and_pattern_retain_the_lambda_caller_newline() {
    use crate::lexical::item::TokenKind;
    for newline in ["\n", "\r\n"] {
        for (prefix, tail, spelling, kind) in [
            ("\\x -> catch v: p", ", q -> value", ",", TokenKind::Comma),
            (
                "\\x -> catch v: p,",
                "q -> value",
                "q",
                TokenKind::Identifier,
            ),
        ] {
            let source = format!("{prefix}{newline}{tail}");
            let (green, exit, _) =
                run_normalized(&source, &OperatorTable::empty(), 0, LineEntry::InLine, None);
            assert_eq!(green.to_string(), prefix, "{source}");
            let Some(NormalizedExit::Complete(Err(Either::Left(item)), _)) = exit else {
                panic!("handler successor remains pending: {source}");
            };
            assert_eq!(item.payload_view().token_kind(), Some(kind));
            assert_eq!(item.payload_view().spelling(), Some(spelling));
            assert!(crate::lexical::observation::implicit_delimited_newline(
                0,
                item.leading_view(),
            ));
            production(&source);
        }
    }
}
