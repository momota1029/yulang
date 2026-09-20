use crate::tests::pattern::recovery::*;

#[test]
fn record_default_expression_slot_is_derived_from_direct_rowan_order() {
    use SyntaxKind::{
        Colon, Comma, Equals, Error, Identifier, LBrace, Missing, OperatorChain, Pattern, RBrace,
        RecordPattern, RecordPatternField as F, Whitespace as W,
    };

    // All ranges below are source-relative; the harness prefixes the Rowan tree.
    fn assert_children(owner: &SyntaxNode, start: usize, expected: &[(SyntaxKind, &str)]) {
        let direct = owner.children_with_tokens().collect::<Vec<_>>();
        assert_eq!(direct.len(), expected.len());
        let mut offset = start;
        for (child, (kind, text)) in direct.iter().zip(expected) {
            assert_eq!(child.kind(), *kind);
            assert_eq!(child.parent(), Some(owner.clone()));
            assert_eq!(child.to_string(), *text);
            assert_eq!(
                child.as_node().is_some(),
                matches!(kind, F | Pattern | OperatorChain | Missing)
            );
            assert_eq!(
                usize::from(child.text_range().start()),
                "sentinel".len() + offset
            );
            offset += text.len();
            assert_eq!(
                usize::from(child.text_range().end()),
                "sentinel".len() + offset
            );
        }
        assert_eq!(
            usize::from(owner.text_range().start()),
            "sentinel".len() + start
        );
        assert_eq!(
            usize::from(owner.text_range().end()),
            "sentinel".len() + offset
        );
    }

    for (source, children, field_children, default_at, separator) in [
        (
            "{a=}",
            vec![(LBrace, "{"), (F, "a="), (RBrace, "}")],
            vec![(Identifier, "a"), (Equals, "="), (OperatorChain, "")],
            Some(3),
            false,
        ),
        (
            "{a= }",
            vec![(LBrace, "{"), (F, "a= "), (RBrace, "}")],
            vec![
                (Identifier, "a"),
                (Equals, "="),
                (W, " "),
                (OperatorChain, ""),
            ],
            Some(4),
            false,
        ),
        (
            "{a=,b}",
            vec![
                (LBrace, "{"),
                (F, "a="),
                (Comma, ","),
                (F, "b"),
                (RBrace, "}"),
            ],
            vec![(Identifier, "a"), (Equals, "="), (OperatorChain, "")],
            Some(3),
            false,
        ),
        (
            "{a: p =}",
            vec![(LBrace, "{"), (F, "a: p ="), (RBrace, "}")],
            vec![
                (Identifier, "a"),
                (Colon, ":"),
                (W, " "),
                (Pattern, "p"),
                (W, " "),
                (Equals, "="),
                (OperatorChain, ""),
            ],
            Some(7),
            false,
        ),
        (
            "{a=@ x}",
            vec![
                (LBrace, "{"),
                (F, "a="),
                (Error, "@"),
                (W, " "),
                (F, "x"),
                (RBrace, "}"),
            ],
            vec![(Identifier, "a"), (Equals, "="), (OperatorChain, "")],
            Some(3),
            true,
        ),
        (
            "{a=1}",
            vec![(LBrace, "{"), (F, "a=1"), (RBrace, "}")],
            vec![(Identifier, "a"), (Equals, "="), (OperatorChain, "1")],
            None,
            false,
        ),
    ] {
        for origin in [0, 41] {
            let fresh = run(
                source,
                Context {
                    origin,
                    ..Context::default()
                },
            );
            assert_eq!(fresh.remainder, "");
            let root = SyntaxNode::new_root(fresh.green);
            assert_eq!(root.to_string(), format!("sentinel{source}"));
            let pattern = root.children().find(|node| node.kind() == Pattern).unwrap();
            let owner = pattern
                .children()
                .find(|node| node.kind() == RecordPattern)
                .unwrap();
            assert_eq!(owner.parent(), Some(pattern.clone()));
            assert_children(&owner, 0, &children);
            let first_field = owner.children().next().unwrap();
            assert_children(&first_field, 1, &field_children);

            let mut observed = Vec::new();
            for child in owner.children_with_tokens() {
                let start = usize::from(child.text_range().start()) - "sentinel".len();
                let end = usize::from(child.text_range().end()) - "sentinel".len();
                match child.kind() {
                    F => {
                        let field = child.into_node().unwrap();
                        if field != first_field {
                            assert_children(&field, start, &[(Identifier, &field.to_string())]);
                        }
                        let direct = field.children_with_tokens().collect::<Vec<_>>();
                        if let Some(equals) = direct.iter().position(|child| child.kind() == Equals)
                        {
                            assert!(direct[equals].as_token().is_some());
                            let mut suffix = direct[equals + 1..]
                                .iter()
                                .filter(|child| child.kind() != W);
                            let expression = suffix.next().unwrap().as_node().unwrap();
                            assert!(suffix.next().is_none());
                            assert_eq!(expression.kind(), OperatorChain);
                            assert_eq!(expression.parent(), Some(field.clone()));
                            if expression.text_range().is_empty() {
                                let at =
                                    usize::from(expression.text_range().start()) - "sentinel".len();
                                assert_children(expression, at, &[(Missing, "")]);
                                let missing = expression.children().next().unwrap();
                                assert_eq!(missing.children_with_tokens().count(), 0);
                                observed.push((StructuralKind::Missing, at..at));
                            }
                        }
                    }
                    Comma => {}
                    Error => {
                        assert!(child.as_token().is_some());
                        observed.push((StructuralKind::ErrorGroup, start..end));
                    }
                    LBrace | RBrace | W => {}
                    kind => panic!("unexpected direct child {kind:?} in {source:?}"),
                }
            }
            let mut expected = Vec::new();
            if let Some(at) = default_at {
                expected.push((StructuralKind::Missing, at..at));
            }
            if separator {
                expected.push((StructuralKind::ErrorGroup, 3..4));
            }
            assert_eq!(observed, expected, "{source:?}");
            // No default Error/retry, duplicate sequence Missing, or recovery
            // hidden inside the accepted nested Pattern/Expression control.
            assert_eq!(
                pattern
                    .descendants_with_tokens()
                    .filter(|child| matches!(child.kind(), Missing | Error | SyntaxKind::Invalid))
                    .count(),
                observed.len(),
                "{source:?}"
            );
        }
    }
}

#[test]
fn record_default_missing_publishes_its_required_expression_wrapper_and_role() {
    for origin in [0, 41] {
        for (source, at) in [
            ("{a=}", 3),
            ("{a =}", 4),
            ("{a=,b}", 3),
            ("{a: p =}", 7),
            ("{a= }", 4),
        ] {
            let fresh = checked(
                source,
                Context {
                    origin,
                    ..Context::default()
                },
                &[fact(false, at..at)],
                source,
                PatternCompletion::Complete,
            );
            let root = SyntaxNode::new_root(fresh.green);
            let missing = root
                .descendants()
                .filter(|node| node.kind() == SyntaxKind::Missing)
                .nth(1)
                .unwrap();
            let expression = missing.parent().unwrap();
            assert_eq!(expression.kind(), SyntaxKind::OperatorChain);
            assert_eq!(expression.to_string(), "");
            assert_eq!(
                expression.parent().unwrap().kind(),
                SyntaxKind::RecordPatternField
            );
            assert_eq!(
                usize::from(expression.text_range().start()),
                "sentinel".len() + at
            );
        }
        // Own RBrace still wins before same-kind carried authority.
        checked(
            "{a= }",
            Context {
                origin,
                closes: PatternCallerCloses::RBRACE,
                ..Context::default()
            },
            &[fact(false, 4..4)],
            "{a= }",
            PatternCompletion::Complete,
        );
    }
}

#[test]
fn record_default_missing_orders_nested_pattern_structured_and_sequence_records() {
    for origin in [0, 41] {
        for (source, expected, completion) in [
            (
                "{a: =}",
                vec![fact(false, 4..4), fact(false, 5..5)],
                PatternCompletion::Incomplete,
            ),
            (
                "{{a=}}",
                vec![invalid_fact(1..5), fact(false, 4..4)],
                PatternCompletion::Complete,
            ),
            (
                "{a=@ x}",
                vec![fact(false, 3..3), fact(true, 3..4)],
                PatternCompletion::Complete,
            ),
            (
                "{a= ",
                vec![fact(false, 4..4), fact(false, 4..4)],
                PatternCompletion::Incomplete,
            ),
        ] {
            checked(
                source,
                Context {
                    origin,
                    ..Context::default()
                },
                &expected,
                source,
                completion,
            );
        }
        checked(
            "{a=]}",
            Context {
                origin,
                ..Context::default()
            },
            &[fact(false, 3..3), fact(true, 3..4)],
            "{a=]}",
            PatternCompletion::Complete,
        );
    }
}

#[test]
fn record_default_missing_preserves_carried_closes_in_both_field_forms() {
    for origin in [0, 41] {
        for prefix in ["{a=", "{a:p="] {
            for gap in [" ", " /*é*/ ", "\r\n "] {
                for (close, closes) in [
                    (")", PatternCallerCloses::RPAREN),
                    ("]", PatternCallerCloses::RBRACKET),
                ] {
                    let suffix = format!("{gap}{close}tail");
                    let source = format!("{prefix}{suffix}");
                    let context = Context {
                        origin,
                        closes,
                        ..Context::default()
                    };
                    let at = prefix.len();
                    let fresh = checked(
                        &source,
                        context,
                        &[fact(false, at..at), fact(false, at..at)],
                        prefix,
                        PatternCompletion::Incomplete,
                    );
                    assert_pending_control(&fresh, &suffix, origin + at, context);
                }
            }
        }
        let source = "({a= /*é*/ )";
        let fresh = checked(
            source,
            Context {
                origin,
                ..Context::default()
            },
            &[fact(false, 4..4), fact(false, 4..4)],
            source,
            PatternCompletion::Incomplete,
        );
        let root = SyntaxNode::new_root(fresh.green);
        for token in root
            .descendants_with_tokens()
            .filter_map(|element| element.into_token())
        {
            if matches!(
                token.kind(),
                SyntaxKind::RParen | SyntaxKind::Whitespace | SyntaxKind::BlockComment
            ) {
                assert_eq!(
                    token.parent().unwrap().kind(),
                    SyntaxKind::ParenthesizedPattern
                );
            }
        }
    }
}

#[test]
fn record_default_missing_fences_keep_whole_items_and_order_before_record_close() {
    let fence = FenceBoundary {
        opener: FenceOpener {
            line: 0,
            marker: 0..3,
            marker_width: 3,
        },
        prefix_policy: FencePrefixPolicy::ActivePrefixQuote { depth: 2, base: 0 },
        close_column: 0,
    };
    for origin in [0, 8_000] {
        for prefix in ["{a=", "{a:p="] {
            for suffix in ["\r\n> > ```\r\nouter", "\r\n> ]\r\nouter", ""] {
                let source = format!("{prefix}{suffix}");
                let context = Context {
                    origin,
                    fence: Some(&fence),
                    ..Context::default()
                };
                let at = prefix.len();
                let fresh = checked(
                    &source,
                    context,
                    &[fact(false, at..at), fact(false, at..at)],
                    prefix,
                    PatternCompletion::Incomplete,
                );
                assert_pending_control(&fresh, suffix, origin + prefix.len(), context);
            }
        }
    }
}

#[test]
fn record_default_accepted_expression_controls_retain_canonical_products() {
    // Authoritative default Expression grammar; literals use the direct cone.
    for source in [
        "{a=1}",
        "{a=1,b=2}",
        "{a:p=1}",
        "{a=\n1,b}",
        "{a= \"x\"}",
        "{a= ~\"r\"}",
        "{a={x}}",
        "{a=f: x,b}",
        "{outer: {x=1} = fallback}",
    ] {
        let fresh = checked(
            source,
            Context::default(),
            &[],
            source,
            PatternCompletion::Complete,
        );
        assert_eq!(fresh.remainder, "");
        let root = SyntaxNode::new_root(fresh.green);
        assert!(root.descendants().any(|node| {
            node.kind() == SyntaxKind::OperatorChain
                && node
                    .parent()
                    .is_some_and(|parent| parent.kind() == SyntaxKind::RecordPatternField)
        }));
    }
}

#[test]
fn record_default_exact_equals_rejection_preserves_the_original_literal_controls() {
    use crate::lexical::lexer::scan_exact_equals;
    let operators = OperatorTable::empty();
    for source in ["{a=\"x\"}", "{a=~\"r\"}"] {
        let recover = Recover::new_for_test(&operators);
        let mark = crate::cursor::LexRecover::new_for_test(recover.operators()).mark();
        let original = source.strip_prefix("{a").unwrap();
        let mut suffix = original;
        let mut lexical_view = crate::cursor::LexRecover::new_for_test(recover.operators());
        let mut lex: crate::cursor::LexIn =
            chasa_recover::In::new(&mut suffix, &mut lexical_view, ());
        assert!(lex.token(scan_exact_equals).is_none());
        assert!(std::ptr::eq(suffix, original));
        assert_eq!(
            crate::cursor::LexRecover::new_for_test(recover.operators()).mark(),
            mark
        );
        assert!(std::ptr::eq(recover.operators(), &operators));

        // The complete malformed source stays covered; no default owner is
        // entered. Literal-owned raw recovery remains an open SCC obligation.
        let fresh = run(source, Context::default());
        assert_eq!(fresh.green.to_string(), format!("sentinel{source}"));
        let root = SyntaxNode::new_root(fresh.green);
        assert!(
            root.descendants_with_tokens()
                .any(|node| matches!(node.kind(), SyntaxKind::Error | SyntaxKind::Invalid))
        );
        assert!(
            !root
                .descendants_with_tokens()
                .any(|element| element.kind() == SyntaxKind::Equals)
        );
    }
}
