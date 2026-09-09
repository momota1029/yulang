use crate::recovery_record::{ConstructRole, Delimiter, PunctuationEvidence};
use crate::tests::pattern::recovery::delimited::close_record;
use crate::tests::pattern::recovery::*;

#[test]
fn record_wrong_kind_literal_keeps_its_inner_brace_and_following_field() {
    let source = "{\"\"\"}\"\"\", a}";
    for origin in [0, 41] {
        let fresh = checked(
            source,
            Context {
                origin,
                ..Context::default()
            },
            &[record(
                1,
                PatternRole::RecordItem,
                origin + 1..origin + 8,
                true,
            )],
            source,
            PatternCompletion::Complete,
        );
        assert_eq!(fresh.remainder, "");
        let root = SyntaxNode::new_root(fresh.green);
        let error = root
            .descendants()
            .find(|node| node.kind() == SyntaxKind::Invalid)
            .unwrap();
        assert_eq!(error.to_string(), "\"\"\"}\"\"\"");
        assert_eq!(error.children().next().unwrap().kind(), SyntaxKind::Pattern);
        let literal = error
            .descendants()
            .find(|node| node.kind() == SyntaxKind::StringLiteral)
            .unwrap();
        assert!(
            literal
                .children_with_tokens()
                .any(|element| element.kind() == SyntaxKind::StringText
                    && element.to_string() == "}")
        );
        let owner = error.parent().unwrap();
        let field = owner
            .children()
            .find(|node| node.kind() == SyntaxKind::RecordPatternField)
            .unwrap();
        assert_eq!(field.to_string(), "a");
        let close = owner.last_child_or_token().unwrap();
        assert_eq!(close.kind(), SyntaxKind::RBrace);
        assert_eq!(
            usize::from(close.text_range().start()),
            "sentinel".len() + 11
        );
    }
}

#[test]
fn delimited_literal_items_follow_the_authorized_comma_or_layout_grammar() {
    // LC-5 literal primaries and the established Pattern sequence grammar.
    for source in [
        "[\"a\",\"b\"]",
        "[a\n\"b\"]",
        "[a\n\"\"\"}\"\"\"]",
        "(a\n\"b\")",
        "(a\n\"\"\"}\"\"\")",
    ] {
        let fresh = checked(
            source,
            Context::default(),
            &[],
            source,
            PatternCompletion::Complete,
        );
        assert_eq!(fresh.remainder, "");
    }
}

#[test]
fn sequence_error_runs_retry_without_duplicate_item_or_separator_missing() {
    use PatternRole::{
        ListSeparator as L, ParenthesizedSeparator as P, RecordItem as I, RecordSeparator as R,
    };
    for origin in [0, 41] {
        for (source, role, range) in [
            ("{@,a}", I, 1..2),
            ("{@ @ a}", I, 1..4),
            ("{@}", I, 1..2),
            ("{a; b}", R, 2..3),
            ("{a @ ; . b}", R, 3..8),
            ("{a;}", R, 2..3),
            ("(a; b)", P, 2..3),
            ("[a; b]", L, 2..3),
            ("[a @ ; b]", L, 3..6),
            ("[a; ,b]", L, 2..3),
        ] {
            let fresh = checked(
                source,
                Context {
                    origin,
                    ..Context::default()
                },
                &[record(
                    1,
                    role,
                    origin + range.start..origin + range.end,
                    true,
                )],
                source,
                PatternCompletion::Complete,
            );
            let root = SyntaxNode::new_root(fresh.green);
            let error = recovery_groups(&root).into_iter().next().unwrap();
            assert_eq!(error.to_string(), source[range.clone()]);
            assert_eq!(
                error.parent().unwrap().kind(),
                match role {
                    L => SyntaxKind::ListPattern,
                    P => SyntaxKind::ParenthesizedPattern,
                    _ => SyntaxKind::RecordPattern,
                }
            );
            for token in error
                .children_with_tokens()
                .filter_map(|element| element.into_token())
            {
                assert_eq!(token.kind(), SyntaxKind::Error);
            }
        }
        checked(
            "{@,,a}",
            Context {
                origin,
                ..Context::default()
            },
            &[
                record(1, I, origin + 1..origin + 2, true),
                record(2, I, origin + 3..origin + 3, false),
            ],
            "{@,,a}",
            PatternCompletion::Incomplete,
        );
    }
}

#[test]
fn record_wrong_kind_primaries_are_structured_in_both_sequence_phases() {
    // A same-line colon is owned by the preceding field, not its separator.
    checked(
        "{a :tag, b}",
        Context::default(),
        &[],
        "{a :tag, b}",
        PatternCompletion::Complete,
    );
    for origin in [0, 41] {
        for head in [
            "1",
            ":tag",
            "(A)",
            "[A]",
            "{x}",
            "(A) as x",
            "\"r\"",
            "\"\"\"}\"\"\"",
        ] {
            for (prefix, role) in [
                ("{", PatternRole::RecordItem),
                ("{a ", PatternRole::RecordSeparator),
            ] {
                let prefix = if head == ":tag" && role == PatternRole::RecordSeparator {
                    "{a\n"
                } else {
                    prefix
                };
                let source = format!("{prefix}{head}, b}}");
                let start = prefix.len();
                let fresh = checked(
                    &source,
                    Context {
                        origin,
                        ..Context::default()
                    },
                    &[record(
                        1,
                        role,
                        origin + start..origin + start + head.len(),
                        true,
                    )],
                    &source,
                    PatternCompletion::Complete,
                );
                let root = SyntaxNode::new_root(fresh.green);
                let error = root
                    .descendants()
                    .find(|node| node.kind() == SyntaxKind::Invalid)
                    .unwrap();
                assert_eq!(error.to_string(), head);
                assert_eq!(error.children().next().unwrap().kind(), SyntaxKind::Pattern);
                assert_eq!(error.parent().unwrap().kind(), SyntaxKind::RecordPattern);
                assert_eq!(
                    error.next_sibling_or_token().unwrap().kind(),
                    SyntaxKind::Comma
                );
            }
        }
    }
}

#[test]
fn record_structured_errors_reserve_outer_records_before_nested_recovery() {
    use ConstructRole::ParenthesizedPattern as P;
    use Delimiter::Parenthesis;
    use PatternRole::{ParenthesizedElement as E, RecordItem as I};
    for origin in [0, 41] {
        for (source, expected, completion) in [
            (
                "{(A}",
                vec![
                    record(1, I, origin + 1..origin + 3, true),
                    close_record(2, P, Parenthesis, origin + 3),
                ],
                PatternCompletion::Incomplete,
            ),
            (
                "{{1}}",
                vec![
                    record(1, I, origin + 1..origin + 4, true),
                    record(2, I, origin + 2..origin + 3, true),
                ],
                PatternCompletion::Complete,
            ),
            (
                "{@ (A}",
                vec![
                    record(1, I, origin + 1..origin + 2, true),
                    record(2, I, origin + 3..origin + 5, true),
                    close_record(3, P, Parenthesis, origin + 5),
                ],
                PatternCompletion::Incomplete,
            ),
            (
                "{(@ a}",
                vec![
                    record(1, I, origin + 1..origin + 5, true),
                    record(2, E, origin + 2..origin + 3, true),
                    close_record(3, P, Parenthesis, origin + 5),
                ],
                PatternCompletion::Incomplete,
            ),
        ] {
            let fresh = checked(
                source,
                Context {
                    origin,
                    ..Context::default()
                },
                &expected,
                source,
                completion,
            );
            let root = SyntaxNode::new_root(fresh.green);
            let errors = root
                .descendants()
                .filter(|node| node.kind() == SyntaxKind::Invalid)
                .collect::<Vec<_>>();
            let outer = errors
                .iter()
                .find(|node| {
                    node.children()
                        .any(|child| child.kind() == SyntaxKind::Pattern)
                })
                .unwrap();
            assert_eq!(outer.parent().unwrap().kind(), SyntaxKind::RecordPattern);
            if source == "{{1}}" {
                assert!(errors[1].ancestors().any(|ancestor| ancestor == *outer));
                assert_eq!(errors[1].to_string(), "1");
            }
            let last = root
                .descendants_with_tokens()
                .filter_map(|element| element.into_token())
                .last()
                .unwrap();
            assert_eq!(last.kind(), SyntaxKind::RBrace);
            assert_eq!(
                last.parent().unwrap().parent().unwrap().kind(),
                SyntaxKind::Pattern
            );
        }
    }
}

#[test]
fn sequence_unclaimed_closes_publish_native_evidence_in_both_phases() {
    use ConstructRole::{ListPattern as L, ParenthesizedPattern as P, RecordPattern as R};
    use Delimiter::{Brace, Bracket, Parenthesis};
    for origin in [0, 41] {
        for (source, owner, expected, actual, range, kind) in [
            ("(])", P, Parenthesis, Bracket, 1..2, SyntaxKind::RBracket),
            ("(a ])", P, Parenthesis, Bracket, 2..4, SyntaxKind::RBracket),
            ("[)]", L, Bracket, Parenthesis, 1..2, SyntaxKind::RParen),
            ("[a }]", L, Bracket, Brace, 2..4, SyntaxKind::RBrace),
            ("{]}", R, Brace, Bracket, 1..2, SyntaxKind::RBracket),
            ("{a )}", R, Brace, Parenthesis, 2..4, SyntaxKind::RParen),
        ] {
            let range = origin + range.start..origin + range.end;
            let mut expected = close_record(1, owner, expected, range.start);
            expected.kind = RecoveryKind::Error;
            expected.site.range = range.clone();
            Arc::make_mut(&mut expected.expectations)[0].range = range.clone();
            expected.unexpected = Arc::from([UnexpectedSyntax::Token {
                range,
                category: UnexpectedCategory::Punctuation(PunctuationEvidence::Close(actual)),
            }]);
            let fresh = checked(
                source,
                Context {
                    origin,
                    ..Context::default()
                },
                &[expected],
                source,
                PatternCompletion::Complete,
            );
            let root = SyntaxNode::new_root(fresh.green);
            let error = recovery_groups(&root).into_iter().next().unwrap();
            assert_eq!(error.last_token().unwrap().kind(), SyntaxKind::Error);
            assert_eq!(
                error.last_token().unwrap().text(),
                match kind {
                    SyntaxKind::RBracket => "]",
                    SyntaxKind::RBrace => "}",
                    SyntaxKind::RParen => ")",
                    _ => unreachable!(),
                }
            );
            assert_eq!(
                error.next_sibling_or_token().unwrap().to_string(),
                &source[source.len() - 1..]
            );
        }
    }
}

#[test]
fn sequence_error_handoff_preserves_whole_caller_items_and_eof_extent() {
    use ConstructRole::{ListPattern as L, ParenthesizedPattern as P, RecordPattern as R};
    use Delimiter::{Brace, Bracket, Parenthesis};
    for origin in [0, 41] {
        for gap in [" ", " /*é*/ ", "\r\n "] {
            for (prefix, owner, delimiter, role, start) in [
                ("{@", R, Brace, PatternRole::RecordItem, 1),
                (
                    "(a;",
                    P,
                    Parenthesis,
                    PatternRole::ParenthesizedSeparator,
                    2,
                ),
                ("[a;", L, Bracket, PatternRole::ListSeparator, 2),
            ] {
                let suffix = format!("{gap})tail");
                // Parenthesized's same-kind local close wins even if carried,
                // so use a bracket witness for that owner instead.
                let suffix = if delimiter == Parenthesis {
                    format!("{gap}]tail")
                } else {
                    suffix
                };
                let context = Context {
                    origin,
                    closes: if delimiter == Parenthesis {
                        PatternCallerCloses::RBRACKET
                    } else {
                        PatternCallerCloses::RPAREN
                    },
                    ..Context::default()
                };
                let source = format!("{prefix}{suffix}");
                let fresh = checked(
                    &source,
                    context,
                    &[
                        record(1, role, origin + start..origin + prefix.len(), true),
                        close_record(2, owner, delimiter, origin + prefix.len()),
                    ],
                    prefix,
                    PatternCompletion::Incomplete,
                );
                assert_pending_control(&fresh, &suffix, origin + prefix.len(), context);
            }
            let prefix = "{(A";
            let suffix = format!("{gap}]tail");
            let source = format!("{prefix}{suffix}");
            let context = Context {
                origin,
                closes: PatternCallerCloses::RBRACKET,
                ..Context::default()
            };
            let fresh = checked(
                &source,
                context,
                &[
                    record(1, PatternRole::RecordItem, origin + 1..origin + 3, true),
                    close_record(2, P, Parenthesis, origin + 3),
                    close_record(3, R, Brace, origin + 3),
                ],
                prefix,
                PatternCompletion::Incomplete,
            );
            assert_pending_control(&fresh, &suffix, origin + prefix.len(), context);
        }
        checked(
            "{@  ",
            Context {
                origin,
                ..Context::default()
            },
            &[
                record(1, PatternRole::RecordItem, origin + 1..origin + 2, true),
                close_record(2, R, Brace, origin + 4),
            ],
            "{@  ",
            PatternCompletion::Incomplete,
        );
        checked(
            "{(A  ",
            Context {
                origin,
                ..Context::default()
            },
            &[
                record(1, PatternRole::RecordItem, origin + 1..origin + 5, true),
                close_record(2, P, Parenthesis, origin + 5),
                close_record(3, R, Brace, origin + 5),
            ],
            "{(A  ",
            PatternCompletion::Incomplete,
        );
    }
}

#[test]
fn sequence_error_fences_preserve_pending_items_and_structured_emitted_bounds() {
    use ConstructRole::{ListPattern as L, ParenthesizedPattern as P, RecordPattern as R};
    use Delimiter::{Brace, Bracket, Parenthesis};
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
        let context = Context {
            origin,
            fence: Some(&fence),
            ..Context::default()
        };
        for (prefix, owner, delimiter, role, start, nested) in [
            ("{@", R, Brace, PatternRole::RecordItem, 1, false),
            ("[a;", L, Bracket, PatternRole::ListSeparator, 2, false),
            ("{(A", R, Brace, PatternRole::RecordItem, 1, true),
        ] {
            let suffix = "\r\n> > ```\r\nouter";
            let source = format!("{prefix}{suffix}");
            let boundary = origin + prefix.len() + 2;
            let mut expected = vec![record(1, role, origin + start..origin + prefix.len(), true)];
            if nested {
                expected.push(close_record(2, P, Parenthesis, boundary));
            }
            expected.push(close_record(
                1 + expected.len() as u32,
                owner,
                delimiter,
                boundary,
            ));
            let fresh = checked(
                &source,
                context,
                &expected,
                prefix,
                PatternCompletion::Incomplete,
            );
            assert_pending_control(&fresh, suffix, origin + prefix.len(), context);
        }
        for (source, end) in [("{@ \r\n> > @ a}", 10), ("{\"\"\"}\r\n> > x\"\"\", a}", 15)] {
            let fresh = checked(
                source,
                context,
                &[record(
                    1,
                    PatternRole::RecordItem,
                    origin + 1..origin + end,
                    true,
                )],
                source,
                PatternCompletion::Complete,
            );
            let root = SyntaxNode::new_root(fresh.green);
            let groups = recovery_groups(&root);
            assert_eq!(groups.len(), 1);
            assert_eq!(groups[0].text(), &source[1..end]);
            if source.starts_with("{@") {
                assert!(groups[0].children_with_tokens().any(|element| {
                    element.kind() == SyntaxKind::Error && element.to_string() == "> > "
                }));
                assert!(
                    !root
                        .descendants_with_tokens()
                        .any(|element| element.kind() == SyntaxKind::YmQuotePrefix)
                );
            } else {
                let prefix = root
                    .descendants_with_tokens()
                    .find(|element| element.kind() == SyntaxKind::YmQuotePrefix)
                    .unwrap();
                assert!(
                    prefix
                        .ancestors()
                        .any(|node| node.kind() == SyntaxKind::Invalid)
                );
            }
        }
    }
}
