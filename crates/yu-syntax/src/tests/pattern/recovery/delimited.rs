use crate::recovery_record::{ConstructRole, Delimiter, PunctuationEvidence};
use crate::tests::pattern::recovery::*;

pub(super) fn close_record(
    id: u32,
    owner: ConstructRole,
    delimiter: Delimiter,
    at: usize,
) -> CommittedRecoveryRecord {
    let role = GrammarRole::ClosingDelimiter { owner, delimiter };
    CommittedRecoveryRecord {
        id: DiagnosticId(id),
        site: RecoverySiteKey {
            role,
            range: at..at,
        },
        kind: RecoveryKind::Missing,
        unexpected: Arc::from([]),
        expectations: Arc::from([SyntaxExpectation {
            role,
            expected: ExpectedSyntax::Punctuation(PunctuationEvidence::Close(delimiter)),
            range: at..at,
            sources: ExpectationSources::COMMITTED_RECOVERY_RULE,
        }]),
        primary_expectation: 0,
    }
}

#[test]
fn delimited_missing_slots_publish_exact_roles_and_direct_owners() {
    use PatternRole::*;
    for origin in [0, 41] {
        for (source, role, at, parent, completion) in [
            (
                "(,a)",
                ParenthesizedElement,
                1,
                SyntaxKind::Pattern,
                PatternCompletion::Incomplete,
            ),
            (
                "(a b)",
                ParenthesizedSeparator,
                3,
                SyntaxKind::ParenthesizedPattern,
                PatternCompletion::Complete,
            ),
            (
                "[,a]",
                ListItem,
                1,
                SyntaxKind::Pattern,
                PatternCompletion::Incomplete,
            ),
            (
                "[..]",
                ListSpreadRhs,
                3,
                SyntaxKind::Pattern,
                PatternCompletion::Incomplete,
            ),
            (
                "[..,a]",
                ListSpreadRhs,
                3,
                SyntaxKind::Pattern,
                PatternCompletion::Incomplete,
            ),
            (
                "[a b]",
                ListSeparator,
                3,
                SyntaxKind::ListPattern,
                PatternCompletion::Complete,
            ),
            (
                "{,a}",
                RecordItem,
                1,
                SyntaxKind::RecordPattern,
                PatternCompletion::Incomplete,
            ),
            (
                "{a:}",
                RecordNestedPattern,
                3,
                SyntaxKind::Pattern,
                PatternCompletion::Incomplete,
            ),
            (
                "{a: =1}",
                RecordNestedPattern,
                4,
                SyntaxKind::Pattern,
                PatternCompletion::Incomplete,
            ),
            (
                "{..}",
                RecordSpreadRhs,
                3,
                SyntaxKind::Pattern,
                PatternCompletion::Incomplete,
            ),
            (
                "{..,a}",
                RecordSpreadRhs,
                3,
                SyntaxKind::Pattern,
                PatternCompletion::Incomplete,
            ),
            (
                "{a b}",
                RecordSeparator,
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
                &[record(1, role, origin + at..origin + at, false)],
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
fn delimited_child_error_roles_do_not_override_nested_owners() {
    use PatternRole::*;
    for origin in [0, 41] {
        for (source, role, range, error) in [
            ("(@ x)", ParenthesizedElement, 1..2, true),
            ("[@ x]", ListItem, 1..2, true),
            ("[..@ x]", ListSpreadRhs, 3..4, true),
            ("{a:@ x}", RecordNestedPattern, 3..4, true),
            ("{..@ x}", RecordSpreadRhs, 3..4, true),
            ("{a:(@ x)}", ParenthesizedElement, 4..5, true),
            ("[A |]", AlternationRhs, 4..4, false),
            ("[(A as)]", AliasBinding, 6..6, false),
            ("{a: :}", SymbolName, 5..5, false),
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
                    error,
                )],
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
                let node = root
                    .descendants()
                    .find(|node| node.kind() == SyntaxKind::Error)
                    .unwrap();
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
fn delimited_missing_close_order_follows_nested_slot_records() {
    use ConstructRole::{ListPattern as L, ParenthesizedPattern as P, RecordPattern as R};
    use Delimiter::{Brace, Bracket, Parenthesis};
    for origin in [0, 41] {
        for (source, records) in [
            (
                "[(,",
                vec![
                    record(
                        1,
                        PatternRole::ParenthesizedElement,
                        origin + 2..origin + 2,
                        false,
                    ),
                    close_record(2, P, Parenthesis, origin + 3),
                    close_record(3, L, Bracket, origin + 3),
                ],
            ),
            (
                "({a:",
                vec![
                    record(
                        1,
                        PatternRole::RecordNestedPattern,
                        origin + 4..origin + 4,
                        false,
                    ),
                    close_record(2, R, Brace, origin + 4),
                    close_record(3, P, Parenthesis, origin + 4),
                ],
            ),
            (
                "{a:[..,",
                vec![
                    record(1, PatternRole::ListSpreadRhs, origin + 6..origin + 6, false),
                    close_record(2, L, Bracket, origin + 7),
                    close_record(3, R, Brace, origin + 7),
                ],
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
fn delimited_missing_closes_keep_caller_items_and_real_outer_close_ownership() {
    use ConstructRole::{ListPattern as L, ParenthesizedPattern as P, RecordPattern as R};
    use Delimiter::{Brace, Bracket, Parenthesis};
    for origin in [0, 41] {
        for (prefix, owner, delimiter, raw_close, caller, child) in [
            (
                "(",
                P,
                Parenthesis,
                "]",
                PatternCallerCloses::RBRACKET,
                None,
            ),
            ("(a", P, Parenthesis, "}", PatternCallerCloses::RBRACE, None),
            (
                "(@",
                P,
                Parenthesis,
                "]",
                PatternCallerCloses::RBRACKET,
                Some((PatternRole::ParenthesizedElement, 1..2, true)),
            ),
            ("[", L, Bracket, ")", PatternCallerCloses::RPAREN, None),
            ("[a", L, Bracket, "}", PatternCallerCloses::RBRACE, None),
            (
                "[..",
                L,
                Bracket,
                ")",
                PatternCallerCloses::RPAREN,
                Some((PatternRole::ListSpreadRhs, 3..3, false)),
            ),
            ("{", R, Brace, ")", PatternCallerCloses::RPAREN, None),
            ("{a", R, Brace, "]", PatternCallerCloses::RBRACKET, None),
            (
                "{a:",
                R,
                Brace,
                ")",
                PatternCallerCloses::RPAREN,
                Some((PatternRole::RecordNestedPattern, 3..3, false)),
            ),
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
                if let Some((role, range, error)) = &child {
                    expected.push(record(
                        1,
                        *role,
                        origin + range.start..origin + range.end,
                        *error,
                    ));
                }
                expected.push(close_record(
                    1 + expected.len() as u32,
                    owner,
                    delimiter,
                    origin + prefix.len(),
                ));
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
            &[close_record(1, L, Bracket, origin + 4)],
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
                .any(|node| node.kind() == SyntaxKind::Error)
        );
    }
}

#[test]
fn delimited_eof_missing_anchors_follow_only_owned_leading() {
    use ConstructRole::{ListPattern as L, ParenthesizedPattern as P, RecordPattern as R};
    use Delimiter::{Brace, Bracket, Parenthesis};
    for origin in [0, 41] {
        for (prefix, owner, delimiter, child) in [
            ("(", P, Parenthesis, None),
            ("(a", P, Parenthesis, None),
            ("[", L, Bracket, None),
            ("[a", L, Bracket, None),
            ("[..", L, Bracket, Some(PatternRole::ListSpreadRhs)),
            ("{", R, Brace, None),
            ("{a", R, Brace, None),
            ("{a:", R, Brace, Some(PatternRole::RecordNestedPattern)),
        ] {
            let suffix = " /*é*/ \r\n";
            let source = format!("{prefix}{suffix}");
            let at = origin + source.len();
            let mut expected = Vec::new();
            if let Some(role) = child {
                expected.push(record(1, role, at..at, false));
            }
            expected.push(close_record(
                1 + expected.len() as u32,
                owner,
                delimiter,
                at,
            ));
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
            assert!(recover.finish_recoveries_for_test().is_empty());
            let control = crate::handoff::complete(crate::handoff::handoff(item), next_line_entry);
            assert_same_exit(&fresh.exit, &control);
            assert_eq!(fresh.remainder, input);
            assert_eq!(fresh.successor, at);
        }
    }
}

#[test]
fn delimited_quoted_fence_missing_keeps_whole_pending_items_and_inner_first_order() {
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
        for (prefix, owner, delimiter, child) in [
            ("(", P, Parenthesis, None),
            ("(a", P, Parenthesis, None),
            ("[", L, Bracket, None),
            ("[..", L, Bracket, Some(PatternRole::ListSpreadRhs)),
            ("{", R, Brace, None),
            ("{a:", R, Brace, Some(PatternRole::RecordNestedPattern)),
        ] {
            let suffix = "\r\n> > ```\r\nouter";
            let source = format!("{prefix}{suffix}");
            let context = Context {
                origin,
                fence: Some(&fence),
                ..Context::default()
            };
            let at = origin + prefix.len() + 2;
            let mut expected = Vec::new();
            if let Some(role) = child {
                expected.push(record(1, role, at..at, false));
            }
            expected.push(close_record(
                1 + expected.len() as u32,
                owner,
                delimiter,
                at,
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
