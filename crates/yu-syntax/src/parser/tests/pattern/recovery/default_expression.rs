use crate::parser::tests::pattern::recovery::delimited::close_record;
use crate::parser::tests::pattern::recovery::*;
use crate::session::{ConstructRole, Delimiter, PunctuationEvidence};

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
                &[record(
                    1,
                    PatternRole::RecordDefaultExpression,
                    origin + at..origin + at,
                    false,
                )],
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
            &[record(
                1,
                PatternRole::RecordDefaultExpression,
                origin + 4..origin + 4,
                false,
            )],
            "{a= }",
            PatternCompletion::Complete,
        );
    }
}

#[test]
fn record_default_missing_orders_nested_pattern_structured_and_sequence_records() {
    use PatternRole::{
        RecordDefaultExpression as D, RecordItem as I, RecordNestedPattern as N,
        RecordSeparator as S,
    };
    for origin in [0, 41] {
        for (source, expected, completion) in [
            (
                "{a: =}",
                vec![
                    record(1, N, origin + 4..origin + 4, false),
                    record(2, D, origin + 5..origin + 5, false),
                ],
                PatternCompletion::Incomplete,
            ),
            (
                "{{a=}}",
                vec![
                    record(1, I, origin + 1..origin + 5, true),
                    record(2, D, origin + 4..origin + 4, false),
                ],
                PatternCompletion::Complete,
            ),
            (
                "{a=@ x}",
                vec![
                    record(1, D, origin + 3..origin + 3, false),
                    record(2, S, origin + 3..origin + 4, true),
                ],
                PatternCompletion::Complete,
            ),
            (
                "{a= ",
                vec![
                    record(1, D, origin + 4..origin + 4, false),
                    close_record(
                        2,
                        ConstructRole::RecordPattern,
                        Delimiter::Brace,
                        origin + 4,
                    ),
                ],
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
        let mut wrong_close = close_record(
            2,
            ConstructRole::RecordPattern,
            Delimiter::Brace,
            origin + 3,
        );
        wrong_close.kind = RecoveryKind::Error;
        wrong_close.site.range = origin + 3..origin + 4;
        Arc::make_mut(&mut wrong_close.expectations)[0].range = origin + 3..origin + 4;
        wrong_close.unexpected = Arc::from([UnexpectedSyntax::Token {
            range: origin + 3..origin + 4,
            category: UnexpectedCategory::Punctuation(PunctuationEvidence::Close(
                Delimiter::Bracket,
            )),
        }]);
        checked(
            "{a=]}",
            Context {
                origin,
                ..Context::default()
            },
            &[record(1, D, origin + 3..origin + 3, false), wrong_close],
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
                    let at = origin + prefix.len();
                    let fresh = checked(
                        &source,
                        context,
                        &[
                            record(1, PatternRole::RecordDefaultExpression, at..at, false),
                            close_record(2, ConstructRole::RecordPattern, Delimiter::Brace, at),
                        ],
                        prefix,
                        PatternCompletion::Incomplete,
                    );
                    assert_pending_control(&fresh, &suffix, at, context);
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
            &[
                record(
                    1,
                    PatternRole::RecordDefaultExpression,
                    origin + 4..origin + 4,
                    false,
                ),
                close_record(
                    2,
                    ConstructRole::RecordPattern,
                    Delimiter::Brace,
                    origin + 4,
                ),
            ],
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
                let at = origin + prefix.len() + if suffix.is_empty() { 0 } else { 2 };
                let fresh = checked(
                    &source,
                    context,
                    &[
                        record(1, PatternRole::RecordDefaultExpression, at..at, false),
                        close_record(2, ConstructRole::RecordPattern, Delimiter::Brace, at),
                    ],
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
    use crate::parser::input::lexer::scan_exact_equals;
    let operators = OperatorTable::empty();
    for source in ["{a=\"x\"}", "{a=~\"r\"}"] {
        let mut recover = Recover::new(&operators);
        let mark = recover.mark();
        let original = source.strip_prefix("{a").unwrap();
        let mut suffix = original;
        let mut lex: crate::parser::LexIn = In::new(&mut suffix, &mut recover, ());
        assert!(lex.token(scan_exact_equals).is_none());
        assert!(std::ptr::eq(suffix, original));
        assert_eq!(recover.mark(), mark);
        assert!(std::ptr::eq(recover.operators(), &operators));

        // The complete malformed source stays covered; no default owner is
        // entered. Literal-owned raw recovery remains an open SCC obligation.
        let fresh = run(source, Context::default(), None);
        assert_eq!(fresh.green.to_string(), format!("sentinel{source}"));
        assert!(
            !fresh.records.iter().any(|record| record.site.role
                == GrammarRole::Pattern(PatternRole::RecordDefaultExpression))
        );
        let root = SyntaxNode::new_root(fresh.green);
        assert!(
            root.descendants()
                .any(|node| node.kind() == SyntaxKind::Error)
        );
        assert!(
            !root
                .descendants_with_tokens()
                .any(|element| element.kind() == SyntaxKind::Equals)
        );
    }
}
