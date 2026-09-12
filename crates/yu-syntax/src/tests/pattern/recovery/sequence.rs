use crate::recovery_record::{ConstructRole, Delimiter, PunctuationEvidence};
use crate::tests::pattern::recovery::delimited::close_record;
use crate::tests::pattern::recovery::*;

fn foreign_close_record(id: u32, origin: usize, range: Range<usize>) -> CommittedRecoveryRecord {
    let mut close = close_record(id, ConstructRole::RecordPattern, Delimiter::Brace, origin);
    close.kind = RecoveryKind::Error;
    close.site.range = origin + range.start..origin + range.end;
    Arc::make_mut(&mut close.expectations)[0].range = close.site.range.clone();
    close.unexpected = Arc::from([UnexpectedSyntax::Token {
        range: close.site.range.clone(),
        category: UnexpectedCategory::Punctuation(PunctuationEvidence::Close(
            Delimiter::Parenthesis,
        )),
    }]);
    close
}

fn assert_foreign_close_slots(green: GreenNode, source: &str, ranges: &[Range<usize>]) {
    let root = SyntaxNode::new_root(green);
    let slots = root
        .descendants()
        .filter(|node| node.kind() == SyntaxKind::RecordPatternForeignClose)
        .collect::<Vec<_>>();
    assert_eq!(slots.len(), ranges.len(), "{source:?}");
    for (slot, range) in slots.iter().zip(ranges) {
        assert_eq!(slot.parent().unwrap().kind(), SyntaxKind::RecordPattern);
        assert_eq!(slot.to_string(), source[range.clone()]);
        assert_eq!(
            usize::from(slot.text_range().start()),
            "sentinel".len() + range.start
        );
        assert_eq!(
            usize::from(slot.text_range().end()),
            "sentinel".len() + range.end
        );
        let children = slot.children_with_tokens().collect::<Vec<_>>();
        assert!(!children.is_empty());
        assert!(
            children
                .iter()
                .all(|child| child.as_token().is_some() && child.kind() == SyntaxKind::Error)
        );
        assert_eq!(children[0].text_range().start(), slot.text_range().start());
        assert_eq!(
            children.last().unwrap().text_range().end(),
            slot.text_range().end()
        );
    }
}

#[test]
fn record_foreign_close_slot_separates_raw_item_and_each_consumed_close() {
    for origin in [0, 41] {
        for (source, closes, raw, literal) in [
            ("{@1}", vec![], Some(1..2), Some(2)),
            ("{)1}", vec![1..2], None, Some(2)),
            ("{))1}", vec![1..2, 2..3], None, Some(3)),
            ("{)@1}", vec![1..2], Some(2..3), Some(3)),
            ("{)@ @1}", vec![1..2], Some(2..5), Some(5)),
            ("{),a}", vec![1..2], None, None),
            ("{)\r\na}", vec![1..2], None, None),
            ("{ /*é*/\r\n)}", vec![10..11], None, None),
            ("{a /*é*/\r\n)}", vec![2..12], None, None),
        ] {
            let mut expected = closes
                .iter()
                .enumerate()
                .map(|(index, range)| foreign_close_record(1 + index as u32, origin, range.clone()))
                .collect::<Vec<_>>();
            if let Some(range) = raw.clone() {
                expected.push(record(
                    1 + expected.len() as u32,
                    PatternRole::RecordItem,
                    origin + range.start..origin + range.end,
                    true,
                ));
            }
            if let Some(start) = literal {
                expected.push(record(
                    1 + expected.len() as u32,
                    PatternRole::RecordItem,
                    origin + start..origin + start + 1,
                    true,
                ));
            }
            if source == "{),a}" {
                expected.push(record(
                    2,
                    PatternRole::RecordItem,
                    origin + 2..origin + 2,
                    false,
                ));
            }
            let fresh = checked(
                source,
                Context {
                    origin,
                    ..Context::default()
                },
                &expected,
                source,
                if source == "{),a}" {
                    PatternCompletion::Incomplete
                } else {
                    PatternCompletion::Complete
                },
            );
            assert_foreign_close_slots(fresh.green.clone(), source, &closes);
            if let Some(range) = raw {
                let root = SyntaxNode::new_root(fresh.green);
                let owner = root
                    .descendants()
                    .find(|node| node.kind() == SyntaxKind::RecordPattern)
                    .unwrap();
                let direct = owner
                    .children_with_tokens()
                    .filter(|child| child.kind() == SyntaxKind::Error)
                    .map(|child| child.to_string())
                    .collect::<String>();
                assert_eq!(direct, source[range]);
            }
        }
    }
}

#[test]
fn record_foreign_close_slot_excludes_missing_and_protected_boundaries() {
    let fence = FenceBoundary {
        opener: FenceOpener {
            line: 0,
            marker: 0..3,
            marker_width: 3,
        },
        prefix_policy: FencePrefixPolicy::ActivePrefixQuote { depth: 2, base: 0 },
        close_column: 0,
    };
    for origin in [0, 41] {
        for (suffix, fence, closes, at, emitted) in [
            ("  ", None, PatternCallerCloses::NONE, 4, "{)  "),
            (" /*é*/ ]tail", None, PatternCallerCloses::RBRACKET, 2, "{)"),
            (
                "\r\n> > ```\r\nouter",
                Some(&fence),
                PatternCallerCloses::NONE,
                4,
                "{)",
            ),
        ] {
            let source = format!("{{){suffix}");
            let context = Context {
                origin,
                fence,
                closes,
                ..Context::default()
            };
            let fresh = checked(
                &source,
                context,
                &[
                    foreign_close_record(1, origin, 1..2),
                    close_record(
                        2,
                        ConstructRole::RecordPattern,
                        Delimiter::Brace,
                        origin + at,
                    ),
                ],
                emitted,
                PatternCompletion::Incomplete,
            );
            assert_foreign_close_slots(fresh.green.clone(), &source, &[1..2]);
            if emitted == "{)" {
                assert_pending_control(&fresh, suffix, origin + 2, context);
            }
        }
        for source in ["{a}", "[)}]", "(]})"] {
            let fresh = run(
                source,
                Context {
                    origin,
                    ..Context::default()
                },
                None,
            );
            assert_eq!(fresh.green.to_string(), format!("sentinel{source}"));
            assert_foreign_close_slots(fresh.green, source, &[]);
        }
        let source = "{a: {)}}";
        let fresh = checked(
            source,
            Context {
                origin,
                ..Context::default()
            },
            &[foreign_close_record(1, origin, 5..6)],
            source,
            PatternCompletion::Complete,
        );
        assert_foreign_close_slots(fresh.green, source, &[5..6]);
    }
}

fn assert_separator_slot(green: GreenNode, text: &str, start: usize) {
    let root = SyntaxNode::new_root(green);
    let owner = root
        .children()
        .find(|node| node.kind() == SyntaxKind::Pattern)
        .unwrap()
        .children()
        .find(|node| node.kind() == SyntaxKind::RecordPattern)
        .unwrap();
    let slots = owner
        .children()
        .filter(|node| node.kind() == SyntaxKind::RecordPatternSeparator)
        .collect::<Vec<_>>();
    assert_eq!(slots.len(), 1);
    let slot = &slots[0];
    assert_eq!(slot.to_string(), text);
    assert_eq!(
        usize::from(slot.text_range().start()),
        "sentinel".len() + start
    );
    assert_eq!(
        usize::from(slot.text_range().end()),
        "sentinel".len() + start + text.len()
    );
    let children = slot.children_with_tokens().collect::<Vec<_>>();
    assert_eq!(children.len(), 1);
    let invalid = children[0].as_node().unwrap();
    assert_eq!(invalid.kind(), SyntaxKind::Invalid);
    assert_eq!(invalid.text_range(), slot.text_range());
    let children = invalid.children_with_tokens().collect::<Vec<_>>();
    assert_eq!(children.len(), 1);
    assert_eq!(children[0].kind(), SyntaxKind::Pattern);
}

#[test]
fn record_separator_slot_distinguishes_colliding_item_topology() {
    use ConstructRole::RecordPattern;
    use Delimiter::{Brace, Parenthesis};
    for origin in [0, 41] {
        for (source, separator) in [
            ("{a)1}", true),
            ("{a@1}", false),
            ("{a))1}", true),
            ("{a@ @1}", false),
        ] {
            let start = source.find('1').unwrap();
            let first = if separator {
                let mut close = close_record(1, RecordPattern, Brace, origin + 2);
                close.kind = RecoveryKind::Error;
                close.site.range = origin + 2..origin + 3;
                Arc::make_mut(&mut close.expectations)[0].range = close.site.range.clone();
                close.unexpected = Arc::from([UnexpectedSyntax::Token {
                    range: close.site.range.clone(),
                    category: UnexpectedCategory::Punctuation(PunctuationEvidence::Close(
                        Parenthesis,
                    )),
                }]);
                close
            } else {
                record(
                    1,
                    PatternRole::RecordSeparator,
                    origin + 2..origin + start,
                    true,
                )
            };
            let mut expected = vec![first];
            if source == "{a))1}" {
                let mut second = expected[0].clone();
                second.id = DiagnosticId(2);
                second.site.range = origin + 3..origin + 4;
                Arc::make_mut(&mut second.expectations)[0].range = second.site.range.clone();
                second.unexpected = Arc::from([UnexpectedSyntax::Token {
                    range: second.site.range.clone(),
                    category: UnexpectedCategory::Punctuation(PunctuationEvidence::Close(
                        Parenthesis,
                    )),
                }]);
                expected.push(second);
            }
            expected.push(record(
                1 + expected.len() as u32,
                if separator {
                    PatternRole::RecordSeparator
                } else {
                    PatternRole::RecordItem
                },
                origin + start..origin + start + 1,
                true,
            ));
            let fresh = checked(
                source,
                Context {
                    origin,
                    ..Context::default()
                },
                &expected,
                source,
                PatternCompletion::Complete,
            );
            let root = SyntaxNode::new_root(fresh.green.clone());
            let owner = root
                .children()
                .find(|node| node.kind() == SyntaxKind::Pattern)
                .unwrap()
                .children()
                .next()
                .unwrap();
            assert_eq!(owner.kind(), SyntaxKind::RecordPattern);
            let mut kinds = vec![SyntaxKind::LBrace, SyntaxKind::RecordPatternField];
            kinds.extend(std::iter::repeat_n(
                if separator {
                    SyntaxKind::RecordPatternForeignClose
                } else {
                    SyntaxKind::Error
                },
                start - 2,
            ));
            kinds.extend([
                if separator {
                    SyntaxKind::RecordPatternSeparator
                } else {
                    SyntaxKind::Invalid
                },
                SyntaxKind::RBrace,
            ]);
            assert_eq!(
                owner
                    .children_with_tokens()
                    .map(|element| element.kind())
                    .collect::<Vec<_>>(),
                kinds
            );
            if separator {
                assert_separator_slot(fresh.green, "1", start);
            } else {
                let invalid = owner
                    .children()
                    .find(|node| node.kind() == SyntaxKind::Invalid)
                    .unwrap();
                assert_eq!(invalid.to_string(), "1");
                assert_eq!(
                    usize::from(invalid.text_range().start()),
                    "sentinel".len() + start
                );
                assert_eq!(
                    usize::from(invalid.text_range().end()),
                    "sentinel".len() + start + 1
                );
                assert_eq!(invalid.children_with_tokens().count(), 1);
                assert_eq!(invalid.first_child().unwrap().kind(), SyntaxKind::Pattern);
                assert!(
                    !root
                        .descendants()
                        .any(|node| node.kind() == SyntaxKind::RecordPatternSeparator)
                );
            }
        }
    }
}

#[test]
fn record_separator_slot_excludes_leading_and_accepted_layout() {
    for origin in [0, 41] {
        let source = "{a /*é*/\r\n\"é\", b}";
        let start = source.find('"').unwrap();
        let fresh = checked(
            source,
            Context {
                origin,
                ..Context::default()
            },
            &[record(
                1,
                PatternRole::RecordSeparator,
                origin + start..origin + start + "\"é\"".len(),
                true,
            )],
            source,
            PatternCompletion::Complete,
        );
        assert_separator_slot(fresh.green, "\"é\"", start);
        for source in ["{a,b}", "{a\r\nb}", "{a /*é*/, b}", "{a :tag, b}"] {
            let fresh = checked(
                source,
                Context {
                    origin,
                    ..Context::default()
                },
                &[],
                source,
                PatternCompletion::Complete,
            );
            let root = SyntaxNode::new_root(fresh.green);
            assert!(
                !root
                    .descendants()
                    .any(|node| node.kind() == SyntaxKind::RecordPatternSeparator)
            );
        }
    }
}

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
fn record_item_wrong_kind_utf8_literal_is_direct_and_retries_after_comma() {
    for origin in [0, 41] {
        for source in ["{\"é\", a}", "{\r\n /*lead*/ \"é\", a}"] {
            let head = "\"é\"";
            let start = source.find(head).unwrap();
            let fresh = checked(
                source,
                Context {
                    origin,
                    ..Context::default()
                },
                &[record(
                    1,
                    PatternRole::RecordItem,
                    origin + start..origin + start + head.len(),
                    true,
                )],
                source,
                PatternCompletion::Complete,
            );
            let root = SyntaxNode::new_root(fresh.green);
            let owner = root
                .children()
                .find(|node| node.kind() == SyntaxKind::Pattern)
                .unwrap()
                .children()
                .find(|node| node.kind() == SyntaxKind::RecordPattern)
                .unwrap();
            let invalid = owner
                .children()
                .find(|node| node.kind() == SyntaxKind::Invalid)
                .unwrap();
            assert_eq!(invalid.to_string(), head);
            assert_eq!(
                invalid.text_range(),
                rowan::TextRange::new(
                    (("sentinel".len() + start) as u32).into(),
                    (("sentinel".len() + start + head.len()) as u32).into(),
                )
            );
            assert_eq!(invalid.children_with_tokens().count(), 1);
            assert_eq!(invalid.first_child().unwrap().kind(), SyntaxKind::Pattern);
            assert_eq!(invalid.parent(), Some(owner.clone()));
            assert_eq!(
                invalid.next_sibling_or_token().unwrap().kind(),
                SyntaxKind::Comma
            );
            assert!(
                !root
                    .descendants()
                    .any(|node| node.kind() == SyntaxKind::RecordPatternSeparator)
            );
            let field = owner
                .children()
                .find(|node| node.kind() == SyntaxKind::RecordPatternField)
                .unwrap();
            assert_eq!(field.to_string(), "a");
            if source.contains("lead") {
                let leading = root
                    .descendants_with_tokens()
                    .find(|element| element.to_string() == "/*lead*/")
                    .unwrap();
                assert!(leading.ancestors().any(|node| node == owner));
                assert!(!leading.ancestors().any(|node| node == invalid));
                assert!(leading.text_range().end() <= invalid.text_range().start());
            }
        }
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
            assert!(
                !root
                    .descendants()
                    .any(|node| node.kind() == SyntaxKind::RecordPatternSeparator)
            );
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
fn record_raw_sequence_roles_follow_direct_ordered_children() {
    use PatternRole::{RecordItem as I, RecordSeparator as S};
    use SyntaxKind::{
        Comma, Error, LBrace, Missing, RBrace, RecordPatternField as F, Whitespace as W,
    };

    // Exact leaves also expose initial/retry leading outside the raw group and
    // internal leading as Error leaves. Record compatibility is checked separately.
    for (source, children, recovery) in [
        (
            "{a,b}",
            vec![
                (LBrace, "{"),
                (F, "a"),
                (Comma, ","),
                (F, "b"),
                (RBrace, "}"),
            ],
            None,
        ),
        (
            "{,a}",
            vec![
                (LBrace, "{"),
                (Missing, ""),
                (Comma, ","),
                (F, "a"),
                (RBrace, "}"),
            ],
            Some((I, 1..1, false)),
        ),
        (
            "{@ @ a}",
            vec![
                (LBrace, "{"),
                (Error, "@"),
                (Error, " "),
                (Error, "@"),
                (W, " "),
                (F, "a"),
                (RBrace, "}"),
            ],
            Some((I, 1..4, true)),
        ),
        (
            "{@}",
            vec![(LBrace, "{"), (Error, "@"), (RBrace, "}")],
            Some((I, 1..2, true)),
        ),
        (
            "{a,@ b}",
            vec![
                (LBrace, "{"),
                (F, "a"),
                (Comma, ","),
                (Error, "@"),
                (W, " "),
                (F, "b"),
                (RBrace, "}"),
            ],
            Some((I, 3..4, true)),
        ),
        (
            "{a b}",
            vec![
                (LBrace, "{"),
                (F, "a"),
                (W, " "),
                (Missing, ""),
                (F, "b"),
                (RBrace, "}"),
            ],
            Some((S, 3..3, false)),
        ),
        (
            "{a; b}",
            vec![
                (LBrace, "{"),
                (F, "a"),
                (Error, ";"),
                (W, " "),
                (F, "b"),
                (RBrace, "}"),
            ],
            Some((S, 2..3, true)),
        ),
        (
            "{a;}",
            vec![(LBrace, "{"), (F, "a"), (Error, ";"), (RBrace, "}")],
            Some((S, 2..3, true)),
        ),
        (
            "{a @ ; . b}",
            vec![
                (LBrace, "{"),
                (F, "a"),
                (W, " "),
                (Error, "@"),
                (Error, " "),
                (Error, ";"),
                (Error, " "),
                (Error, "."),
                (W, " "),
                (F, "b"),
                (RBrace, "}"),
            ],
            Some((S, 3..8, true)),
        ),
        (
            "{ @ @ a}",
            vec![
                (LBrace, "{"),
                (W, " "),
                (Error, "@"),
                (Error, " "),
                (Error, "@"),
                (W, " "),
                (F, "a"),
                (RBrace, "}"),
            ],
            Some((I, 2..5, true)),
        ),
    ] {
        for origin in [0, 41] {
            let expected = recovery
                .iter()
                .map(|(role, range, error)| {
                    record(1, *role, origin + range.start..origin + range.end, *error)
                })
                .collect::<Vec<_>>();
            let fresh = checked(
                source,
                Context {
                    origin,
                    ..Context::default()
                },
                &expected,
                source,
                if source == "{,a}" {
                    PatternCompletion::Incomplete
                } else {
                    PatternCompletion::Complete
                },
            );
            assert_eq!(fresh.remainder, "");
            let root = SyntaxNode::new_root(fresh.green);
            let owner = root
                .children()
                .find(|node| node.kind() == SyntaxKind::Pattern)
                .unwrap()
                .children()
                .find(|node| node.kind() == SyntaxKind::RecordPattern)
                .unwrap();
            assert!(!owner.descendants().any(|node| matches!(
                node.kind(),
                SyntaxKind::Invalid
                    | SyntaxKind::RecordPatternSeparator
                    | SyntaxKind::RecordPatternForeignClose
            )));
            let direct = owner.children_with_tokens().collect::<Vec<_>>();
            assert_eq!(direct.len(), children.len(), "{source:?}");
            let mut offset = 0;
            for (child, (kind, text)) in direct.iter().zip(&children) {
                assert_eq!(child.kind(), *kind, "{source:?}");
                assert_eq!(
                    child.as_node().is_some(),
                    matches!(kind, F | Missing),
                    "{source:?}"
                );
                assert_eq!(child.parent(), Some(owner.clone()));
                assert_eq!(child.to_string(), *text, "{source:?}");
                let end = offset + text.len();
                assert_eq!(child.to_string(), source[offset..end]);
                assert_eq!(
                    usize::from(child.text_range().start()),
                    "sentinel".len() + offset
                );
                assert_eq!(
                    usize::from(child.text_range().end()),
                    "sentinel".len() + end
                );
                if *kind == Missing {
                    assert_eq!(child.as_node().unwrap().children_with_tokens().count(), 0);
                }
                offset = end;
            }
            assert_eq!(offset, source.len());

            // This bounded schema starts in Item. Comma resets Item, accepted
            // field/spread enters Separator, and trivia preserves the phase.
            // A maximal direct Error group takes its entry phase, then permits
            // Item retry. In particular, an earlier field cannot classify the
            // post-comma group in `{a,@ b}`. Neither spelling nor records select it.
            let mut phase = I;
            let mut observed = Vec::new();
            let mut index = 0;
            while index < direct.len() {
                let child = &direct[index];
                let start = usize::from(child.text_range().start()) - "sentinel".len();
                match child.kind() {
                    Comma => phase = I,
                    F | SyntaxKind::RecordPatternSpreadItem => phase = S,
                    Missing => {
                        observed.push((phase, start..start, false));
                        phase = I;
                    }
                    Error => {
                        let role = phase;
                        let mut end = usize::from(child.text_range().end()) - "sentinel".len();
                        while index + 1 < direct.len() && direct[index + 1].kind() == Error {
                            index += 1;
                            assert_eq!(
                                usize::from(direct[index].text_range().start()),
                                "sentinel".len() + end
                            );
                            end = usize::from(direct[index].text_range().end()) - "sentinel".len();
                        }
                        observed.push((role, start..end, true));
                        phase = I;
                    }
                    LBrace | RBrace | W => {}
                    kind => panic!("unexpected direct child {kind:?} in {source:?}"),
                }
                index += 1;
            }
            assert_eq!(
                observed,
                recovery.iter().cloned().collect::<Vec<_>>(),
                "{source:?}"
            );
        }
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
                let slot = if role == PatternRole::RecordSeparator {
                    let slot = error.parent().unwrap();
                    assert_eq!(slot.kind(), SyntaxKind::RecordPatternSeparator);
                    assert_eq!(slot.children_with_tokens().count(), 1);
                    assert_eq!(slot.text_range(), error.text_range());
                    slot
                } else {
                    error.clone()
                };
                assert_eq!(slot.parent().unwrap().kind(), SyntaxKind::RecordPattern);
                assert_eq!(
                    slot.next_sibling_or_token().unwrap().kind(),
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
                "{a (@ a}",
                vec![
                    record(
                        1,
                        PatternRole::RecordSeparator,
                        origin + 3..origin + 7,
                        true,
                    ),
                    record(2, E, origin + 4..origin + 5, true),
                    close_record(3, P, Parenthesis, origin + 7),
                ],
                PatternCompletion::Incomplete,
            ),
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
            if source == "{a (@ a}" {
                assert_separator_slot(root.green().into_owned(), "(@ a", 3);
            } else {
                assert_eq!(outer.parent().unwrap().kind(), SyntaxKind::RecordPattern);
            }
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
            assert!(
                !root
                    .descendants()
                    .any(|node| node.kind() == SyntaxKind::RecordPatternSeparator)
            );
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
            let next = if owner == R {
                let slot = error.parent().unwrap();
                assert_eq!(slot.kind(), SyntaxKind::RecordPatternForeignClose);
                slot.next_sibling_or_token()
            } else {
                error.next_sibling_or_token()
            };
            assert_eq!(next.unwrap().to_string(), &source[source.len() - 1..]);
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
            for (prefix, role, start) in [
                ("{(A", PatternRole::RecordItem, 1),
                ("{a (A", PatternRole::RecordSeparator, 3),
            ] {
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
                        record(1, role, origin + start..origin + prefix.len(), true),
                        close_record(2, P, Parenthesis, origin + prefix.len()),
                        close_record(3, R, Brace, origin + prefix.len()),
                    ],
                    prefix,
                    PatternCompletion::Incomplete,
                );
                assert_pending_control(&fresh, &suffix, origin + prefix.len(), context);
                if role == PatternRole::RecordSeparator {
                    assert_separator_slot(fresh.green, "(A", start);
                }
            }
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
            ("{a (A", R, Brace, PatternRole::RecordSeparator, 3, true),
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
            if role == PatternRole::RecordSeparator {
                assert_separator_slot(fresh.green, "(A", start);
            }
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
