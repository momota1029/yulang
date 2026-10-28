use crate::tests::pattern::recovery::*;

#[test]
fn delimited_missing_slots_preserve_direct_cst_owners() {
    for origin in [0, 41] {
        for (source, at, parent, completion) in [
            (
                "(,a)",
                1,
                SyntaxKind::Pattern,
                PatternCompletion::Incomplete,
            ),
            (
                "[,a]",
                1,
                SyntaxKind::Pattern,
                PatternCompletion::Incomplete,
            ),
            (
                "[..]",
                3,
                SyntaxKind::Pattern,
                PatternCompletion::Incomplete,
            ),
            (
                "[..,a]",
                3,
                SyntaxKind::Pattern,
                PatternCompletion::Incomplete,
            ),
            (
                "{,a}",
                1,
                SyntaxKind::RecordPattern,
                PatternCompletion::Incomplete,
            ),
            (
                "{a:}",
                3,
                SyntaxKind::Pattern,
                PatternCompletion::Incomplete,
            ),
            (
                "{a: =1}",
                4,
                SyntaxKind::Pattern,
                PatternCompletion::Incomplete,
            ),
            (
                "{..}",
                3,
                SyntaxKind::Pattern,
                PatternCompletion::Incomplete,
            ),
            (
                "{..,a}",
                3,
                SyntaxKind::Pattern,
                PatternCompletion::Incomplete,
            ),
            (
                "{a b}",
                3,
                SyntaxKind::RecordPattern,
                PatternCompletion::Complete,
            ),
        ] {
            let fresh = checked(
                source,
                Context {
                    origin,
                    ..Context::default()
                },
                &[fact(false, at..at)],
                source,
                completion,
            );
            assert_eq!(fresh.remainder, "");
            let root = SyntaxNode::new_root(fresh.green);
            let missing = root
                .descendants()
                .filter(|node| node.kind() == SyntaxKind::Missing)
                .nth(1)
                .unwrap();
            assert_eq!(missing.parent().unwrap().kind(), parent, "{source:?}");
            assert_eq!(
                usize::from(missing.text_range().start()),
                "sentinel".len() + at
            );
        }
    }
}

#[test]
fn delimited_child_errors_do_not_override_nested_owners() {
    for origin in [0, 41] {
        for (source, range, error) in [
            ("(@ x)", 1..2, true),
            ("[@ x]", 1..2, true),
            ("[..@ x]", 3..4, true),
            ("{a:@ x}", 3..4, true),
            ("{..@ x}", 3..4, true),
            ("{a:(@ x)}", 4..5, true),
            ("[A |]", 4..4, false),
            ("[(A as)]", 6..6, false),
            ("{a: :}", 5..5, false),
        ] {
            let fresh = checked(
                source,
                Context {
                    origin,
                    ..Context::default()
                },
                &[fact(error, range)],
                source,
                if error {
                    PatternCompletion::Complete
                } else {
                    PatternCompletion::Incomplete
                },
            );
            assert_eq!(fresh.remainder, "");
            if error {
                let root = SyntaxNode::new_root(fresh.green);
                let node = recovery_groups(&root).into_iter().next().unwrap();
                assert_eq!(node.to_string(), "@");
                assert_eq!(
                    node.next_sibling_or_token().unwrap().kind(),
                    SyntaxKind::Whitespace
                );
                assert_eq!(node.parent().unwrap().kind(), SyntaxKind::Pattern);
            }
        }
    }
}

#[test]
fn delimited_missing_close_order_follows_nested_cst_order() {
    for origin in [0, 41] {
        for (source, records) in [
            (
                "[(,",
                vec![fact(false, 2..2), fact(false, 3..3), fact(false, 3..3)],
            ),
            (
                "({a:",
                vec![fact(false, 4..4), fact(false, 4..4), fact(false, 4..4)],
            ),
            (
                "{a:[..,",
                vec![fact(false, 6..6), fact(false, 7..7), fact(false, 7..7)],
            ),
        ] {
            let fresh = checked(
                source,
                Context {
                    origin,
                    ..Context::default()
                },
                &records,
                source,
                PatternCompletion::Incomplete,
            );
            assert_eq!(fresh.remainder, "");
            assert_eq!(fresh.successor, origin + source.len());
            assert!(matches!(
                fresh.exit,
                NormalizedExit::Complete(Err(Either::Right(_)), _)
            ));
        }
    }
}

#[test]
fn delimited_terminal_close_is_derived_from_direct_rowan_order() {
    use SyntaxKind::{
        Colon, Identifier, LBrace, LBracket, LParen, ListPattern, Missing, ParenthesizedPattern,
        Pattern, RBrace, RBracket, RParen, RecordPattern, RecordPatternField,
    };

    fn assert_children(owner: &SyntaxNode, start: usize, expected: &[(SyntaxKind, &str)]) {
        let direct = owner.children_with_tokens().collect::<Vec<_>>();
        assert_eq!(direct.len(), expected.len());
        let mut at = "sentinel".len() + start;
        for (child, (kind, text)) in direct.iter().zip(expected) {
            assert_eq!(child.kind(), *kind);
            assert_eq!(child.parent(), Some(owner.clone()));
            assert_eq!(child.to_string(), *text);
            assert_eq!(
                child.as_node().is_some(),
                matches!(kind, Pattern | RecordPattern | RecordPatternField | Missing)
            );
            assert_eq!(usize::from(child.text_range().start()), at);
            at += text.len();
            assert_eq!(usize::from(child.text_range().end()), at);
            if *kind == Missing {
                assert_eq!(child.as_node().unwrap().children_with_tokens().count(), 0);
            }
        }
    }

    for origin in [0, 41] {
        for (open, close, owner_kind, child_kind, open_kind, close_kind) in [
            ("(", ")", ParenthesizedPattern, Pattern, LParen, RParen),
            ("[", "]", ListPattern, Pattern, LBracket, RBracket),
            ("{", "}", RecordPattern, RecordPatternField, LBrace, RBrace),
        ] {
            for item in ["", "a"] {
                for has_close in [false, true] {
                    let source = format!("{open}{item}{}", if has_close { close } else { "" });
                    let records = if has_close {
                        vec![]
                    } else {
                        vec![fact(false, source.len()..source.len())]
                    };
                    let fresh = checked(
                        &source,
                        Context {
                            origin,
                            ..Context::default()
                        },
                        &records,
                        &source,
                        if has_close {
                            PatternCompletion::Complete
                        } else {
                            PatternCompletion::Incomplete
                        },
                    );
                    assert_eq!(fresh.remainder, "");
                    let root = SyntaxNode::new_root(fresh.green);
                    assert_eq!(root.to_string(), format!("sentinel{source}"));
                    // Select the slot from its direct CST owner, not recovery records.
                    let pattern = root.children().find(|node| node.kind() == Pattern).unwrap();
                    let owner = pattern
                        .children()
                        .find(|node| node.kind() == owner_kind)
                        .unwrap();
                    let mut expected = vec![(open_kind, open)];
                    if !item.is_empty() {
                        expected.push((child_kind, item));
                    }
                    expected.push(if has_close {
                        (close_kind, close)
                    } else {
                        (Missing, "")
                    });
                    assert_children(&owner, 0, &expected);
                    let recovery = owner
                        .descendants()
                        .filter(|node| {
                            matches!(
                                node.kind(),
                                Missing | SyntaxKind::Error | SyntaxKind::Invalid
                            )
                        })
                        .collect::<Vec<_>>();
                    if has_close {
                        assert!(recovery.is_empty());
                    } else {
                        assert_eq!(recovery, vec![owner.last_child().unwrap()]);
                        assert!(
                            !owner
                                .descendants_with_tokens()
                                .any(|child| child.kind() == close_kind)
                        );
                    }
                }
            }
        }

        let source = "({a:";
        let at = source.len();
        let fresh = checked(
            source,
            Context {
                origin,
                ..Context::default()
            },
            &[
                fact(false, at..at),
                fact(false, at..at),
                fact(false, at..at),
            ],
            source,
            PatternCompletion::Incomplete,
        );
        assert_eq!(fresh.remainder, "");
        let root = SyntaxNode::new_root(fresh.green);
        assert_eq!(root.to_string(), format!("sentinel{source}"));
        let pattern = root.children().find(|node| node.kind() == Pattern).unwrap();
        let paren = pattern
            .children()
            .find(|node| node.kind() == ParenthesizedPattern)
            .unwrap();
        assert_children(&paren, 0, &[(LParen, "("), (Pattern, "{a:"), (Missing, "")]);
        let element = paren.first_child().unwrap();
        assert_children(&element, 1, &[(RecordPattern, "{a:")]);
        let record = element.first_child().unwrap();
        assert_children(
            &record,
            1,
            &[(LBrace, "{"), (RecordPatternField, "a:"), (Missing, "")],
        );
        let field = record.first_child().unwrap();
        assert_children(&field, 2, &[(Identifier, "a"), (Colon, ":"), (Pattern, "")]);
        let nested = field.first_child().unwrap();
        assert_children(&nested, 4, &[(Missing, "")]);
        let missing = paren
            .descendants()
            .filter(|node| node.kind() == Missing)
            .collect::<Vec<_>>();
        assert_eq!(
            missing,
            vec![
                nested.first_child().unwrap(),
                record.last_child().unwrap(),
                paren.last_child().unwrap()
            ]
        );
    }
}

#[test]
fn delimited_missing_closes_keep_caller_items_and_real_outer_close_ownership() {
    for origin in [0, 41] {
        for (prefix, raw_close, caller, child) in [
            ("(", "]", PatternCallerCloses::RBRACKET, None),
            ("(a", "}", PatternCallerCloses::RBRACE, None),
            ("(@", "]", PatternCallerCloses::RBRACKET, Some((1..2, true))),
            ("[", ")", PatternCallerCloses::RPAREN, None),
            ("[a", "}", PatternCallerCloses::RBRACE, None),
            ("[..", ")", PatternCallerCloses::RPAREN, Some((3..3, false))),
            ("{", ")", PatternCallerCloses::RPAREN, None),
            ("{a", "]", PatternCallerCloses::RBRACKET, None),
            ("{a:", ")", PatternCallerCloses::RPAREN, Some((3..3, false))),
        ] {
            for gap in [" ", " /*é*/ ", "\r\n "] {
                let suffix = format!("{gap}{raw_close}tail");
                let source = format!("{prefix}{suffix}");
                let context = Context {
                    origin,
                    closes: caller,
                    ..Context::default()
                };
                let mut expected = Vec::new();
                if let Some((range, error)) = &child {
                    expected.push(fact(*error, range.clone()));
                }
                expected.push(fact(false, prefix.len()..prefix.len()));
                let fresh = checked(
                    &source,
                    context,
                    &expected,
                    prefix,
                    PatternCompletion::Incomplete,
                );
                assert_pending_control(&fresh, &suffix, origin + prefix.len(), context);
            }
        }
        // The actual parenthesis remains native in its enclosing owner.
        let source = "( [a )";
        let fresh = checked(
            source,
            Context {
                origin,
                ..Context::default()
            },
            &[fact(false, 4..4)],
            source,
            PatternCompletion::Incomplete,
        );
        let root = SyntaxNode::new_root(fresh.green);
        let close = root
            .descendants_with_tokens()
            .filter_map(|element| element.into_token())
            .find(|token| token.kind() == SyntaxKind::RParen)
            .unwrap();
        assert_eq!(
            close.parent().unwrap().kind(),
            SyntaxKind::ParenthesizedPattern
        );
        assert!(
            !close
                .parent_ancestors()
                .any(|node| matches!(node.kind(), SyntaxKind::Error | SyntaxKind::Invalid))
        );
    }
}

#[test]
fn delimited_eof_missing_anchors_follow_only_owned_leading() {
    for origin in [0, 41] {
        for (prefix, child) in [
            ("(", false),
            ("(a", false),
            ("[", false),
            ("[a", false),
            ("[..", true),
            ("{", false),
            ("{a", false),
            ("{a:", true),
        ] {
            let suffix = " /*é*/ \r\n";
            let source = format!("{prefix}{suffix}");
            let at = source.len();
            let mut expected = Vec::new();
            if child {
                expected.push(fact(false, at..at));
            }
            expected.push(fact(false, at..at));
            let fresh = checked(
                &source,
                Context {
                    origin,
                    ..Context::default()
                },
                &expected,
                &source,
                PatternCompletion::Incomplete,
            );
            let operators = OperatorTable::empty();
            let recover = Recover::new_for_test(&operators);
            let mut input = suffix;
            let CurrentItem {
                mut item,
                next_line_entry,
            } = current_item(
                chasa_recover::In::new(
                    &mut input,
                    &mut crate::cursor::LexRecover::new_for_test(recover.operators()),
                    (),
                ),
                origin + prefix.len(),
                LineEntry::InLine,
                None,
                |lex, leading, at, fence, _| scan_pattern_payload(lex, leading, at, fence, 0),
            )
            .unwrap();
            let mut owner_output = GreenNodeBuilder::new();
            owner_output.start_node(SyntaxKind::Root.into());
            item.emit_all_remaining_leading(&mut owner_output);
            owner_output.finish_node();
            assert_eq!(owner_output.finish().to_string(), suffix);
            let control = crate::handoff::complete(crate::handoff::handoff(item), next_line_entry);
            assert_same_exit(&fresh.exit, &control);
            assert_eq!(fresh.remainder, input);
            assert_eq!(fresh.successor, origin + at);
        }
    }
}

#[test]
fn delimited_quoted_fence_missing_keeps_whole_pending_items_and_inner_first_order() {
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
        for (prefix, child) in [
            ("(", false),
            ("(a", false),
            ("[", false),
            ("[..", true),
            ("{", false),
            ("{a:", true),
        ] {
            let suffix = "\r\n> > ```\r\nouter";
            let source = format!("{prefix}{suffix}");
            let context = Context {
                origin,
                fence: Some(&fence),
                ..Context::default()
            };
            let at = prefix.len();
            let mut expected = Vec::new();
            if child {
                expected.push(fact(false, at..at));
            }
            expected.push(fact(false, at..at));
            let fresh = checked(
                &source,
                context,
                &expected,
                prefix,
                PatternCompletion::Incomplete,
            );
            assert_pending_control(&fresh, suffix, origin + prefix.len(), context);
        }
    }
}

#[test]
fn delimited_accepted_layout_spread_and_default_controls_add_no_records() {
    // Current authoritative comma-or-layout grammar; semantic validation of
    // duplicate names and spread cardinality is not syntax recovery.
    for source in [
        "()",
        "(a,)",
        "(a\nb)",
        "(\n  a\n  b\n)",
        "[]",
        "[a,]",
        "[a\nb]",
        "[..a, b, ..c]",
        "[\n  a\n  ..b\n]",
        "{}",
        "{a,}",
        "{a\nb}",
        "{a, b:p, c=1, ..r}",
        "{a:p = 1}",
        "{a,a}",
    ] {
        let fresh = checked(
            source,
            Context::default(),
            &[],
            source,
            PatternCompletion::Complete,
        );
        assert_eq!(fresh.remainder, "");
        assert!(matches!(
            fresh.exit,
            NormalizedExit::Complete(Err(Either::Right(_)), _)
        ));
    }
}
