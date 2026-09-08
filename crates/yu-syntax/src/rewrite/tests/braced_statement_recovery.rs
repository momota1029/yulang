use super::*;
use crate::{rewrite::ambient_claim::AmbientClaimView, session::*};
use std::{ops::Range, sync::Arc};

fn parse<'s>(
    source: &'s str,
    origin: usize,
    fence: Option<&FenceBoundary>,
    frozen: Option<&[CommittedRecoveryRecord]>,
) -> (
    GreenNode,
    Vec<CommittedRecoveryRecord>,
    NormalizedExit,
    &'s str,
) {
    let operators = OperatorTable::empty();
    let mut recover = Recover::new(&operators);
    let mut input = source;
    let mut output = frozen
        .map(GreenNodeBuilder::reconcile)
        .unwrap_or_else(GreenNodeBuilder::new);
    output.start_node(SyntaxKind::Root.into());
    let exit = statement_normalized(
        In::new(&mut input, &mut recover, &mut output),
        0,
        0,
        origin,
        LineEntry::InLine,
        fence,
        Some(AmbientClaimView::root_statement(0)).into(),
        Some(crate::rewrite::sequence::SequenceOwner::RootStatement),
    );
    output.finish_node();
    let (green, records) = output.finish_with_recoveries();
    (green, records, exit, input)
}

fn record(
    id: usize,
    role: GrammarRole,
    range: Range<usize>,
    error: bool,
) -> CommittedRecoveryRecord {
    let expected = match role {
        GrammarRole::BracedStatementBlock(BracedStatementBlockRole::Statement) => {
            ExpectedSyntax::Statement
        }
        GrammarRole::BracedStatementBlock(BracedStatementBlockRole::Separator) => {
            ExpectedSyntax::StatementSeparator
        }
        GrammarRole::ClosingDelimiter { delimiter, .. } => {
            ExpectedSyntax::Punctuation(PunctuationEvidence::Close(delimiter))
        }
        _ => unreachable!(),
    };
    CommittedRecoveryRecord {
        id: DiagnosticId(id as u32),
        site: RecoverySiteKey {
            role,
            range: range.clone(),
        },
        kind: if error {
            RecoveryKind::Error
        } else {
            RecoveryKind::Missing
        },
        unexpected: if error {
            Arc::from([UnexpectedSyntax::Token {
                range: range.clone(),
                category: UnexpectedCategory::OtherCharacter,
            }])
        } else {
            Arc::from([])
        },
        expectations: Arc::from([SyntaxExpectation {
            role,
            expected,
            range,
            sources: ExpectationSources::COMMITTED_RECOVERY_RULE,
        }]),
        primary_expectation: 0,
    }
}

#[test]
fn braced_slots_have_exact_shifted_and_frozen_records() {
    let statement = GrammarRole::BracedStatementBlock(BracedStatementBlockRole::Statement);
    let separator = GrammarRole::BracedStatementBlock(BracedStatementBlockRole::Separator);
    let close = GrammarRole::ClosingDelimiter {
        owner: ConstructRole::BracedStatementBlockExpression,
        delimiter: Delimiter::Brace,
    };
    for (source, slots) in [
        (
            "{,;}",
            vec![(statement, 1..1, false), (statement, 2..2, false)],
        ),
        ("{ @ @ α}", vec![(statement, 2..5, true)]),
        ("{@,}", vec![(statement, 1..2, true)]),
        (
            "{@\n,}",
            vec![(statement, 1..2, true), (statement, 3..3, false)],
        ),
        (
            "{@\r\n;}",
            vec![(statement, 1..2, true), (statement, 4..4, false)],
        ),
        ("{x\n;}", vec![(statement, 3..3, false)]),
        ("{x\r\n,}", vec![(statement, 4..4, false)]),
        ("{@}", vec![(statement, 1..2, true)]),
        ("{@  ", vec![(statement, 1..2, true), (close, 4..4, false)]),
        ("{  ", vec![(close, 3..3, false)]),
        ("{use a use b}", vec![(separator, 6..6, false)]),
    ] {
        for origin in [0, 137] {
            let expected: Vec<_> = slots
                .iter()
                .enumerate()
                .map(|(id, (role, range, error))| {
                    record(id, *role, origin + range.start..origin + range.end, *error)
                })
                .collect();
            let (green, records, _, _) = parse(source, origin, None, None);
            assert_eq!(green.to_string(), source);
            assert_eq!(records, expected, "{source:?}");
            let (again, frozen, _, _) = parse(source, origin, None, Some(&records));
            assert_eq!(again, green);
            assert_eq!(frozen, records);
        }
    }
}

#[test]
fn protected_nonlocal_closes_keep_horizontal_and_crlf_leading() {
    for prefix in ["{", "{@", "{x;", "{x"] {
        for leading in ["  ", "\r\n  "] {
            for close in [')', ']'] {
                let source = format!("{prefix}{leading}{close}tail");
                let (green, records, exit, suffix) = parse(&source, 100, None, None);
                assert_eq!(green.to_string(), prefix);
                assert_eq!(suffix, "tail");
                let NormalizedExit::Complete(Err(Either::Left(item)), _) = exit else {
                    panic!("protected close")
                };
                assert_eq!(
                    item.extent(100 + source.len() - suffix.len())
                        .recovery_range(),
                    100 + prefix.len()..100 + prefix.len() + leading.len() + 1
                );
                assert_eq!(
                    records.last().unwrap().site.range,
                    100 + prefix.len()..100 + prefix.len()
                );
            }
        }
    }
}

#[test]
fn accepted_braced_sequence_controls_stay_record_free() {
    for source in [
        "{}", "{ }", "{x;}", "{x,}", "{x;  ", "{f x}", "{f: x,y}", "{x\n y}",
    ] {
        let (green, records, _, _) = parse(source, 0, None, None);
        assert_eq!(green.to_string(), source);
        if source.ends_with('}') {
            assert!(records.is_empty(), "{source:?}: {records:?}");
        } else {
            assert_eq!(records.len(), 1);
        }
    }
}

#[test]
fn declaration_body_callers_publish_the_braced_child_role() {
    for prefix in ["mod M ", "role R ", "impl T ", "act A ", "for x in xs "] {
        let source = format!("{prefix}{{ @ }}");
        let (green, records, _, _) = parse(&source, 0, None, None);
        assert_eq!(green.to_string(), source);
        assert_eq!(
            records,
            [record(
                0,
                GrammarRole::BracedStatementBlock(BracedStatementBlockRole::Statement),
                prefix.len() + 2..prefix.len() + 3,
                true
            )],
            "{source:?}"
        );
        let (again, frozen, _, _) = parse(&source, 0, None, Some(&records));
        assert_eq!(again, green);
        assert_eq!(frozen, records);
    }
}

#[test]
fn declaration_body_callers_return_protected_closes_with_leading() {
    let role = GrammarRole::ClosingDelimiter {
        owner: ConstructRole::BracedStatementBlockExpression,
        delimiter: Delimiter::Brace,
    };
    for prefix in ["mod M ", "role R ", "impl T ", "act A ", "for x in xs "] {
        for leading in ["  ", "\r\n  "] {
            for close in [')', ']'] {
                let owned = format!("{prefix}{{x");
                let source = format!("{owned}{leading}{close}tail");
                let (green, records, exit, suffix) = parse(&source, 100, None, None);
                assert_eq!(green.to_string(), owned, "{source:?}");
                let at = 100 + owned.len();
                assert_eq!(records, [record(0, role, at..at, false)], "{source:?}");
                let NormalizedExit::Complete(Err(Either::Left(item)), _) = exit else {
                    panic!("protected close: {source:?}")
                };
                assert_eq!(suffix, "tail");
                assert_eq!(
                    item.extent(100 + source.len() - suffix.len())
                        .recovery_range(),
                    at..at + leading.len() + 1
                );
                let (again, frozen, _, remainder) = parse(&source, 100, None, Some(&records));
                assert_eq!(again, green);
                assert_eq!(frozen, records);
                assert_eq!(remainder, suffix);
            }
        }
    }
}

#[test]
fn error_run_stops_at_quoted_fence_and_qualifying_newline() {
    use crate::rewrite::yumark::{FenceOpener, FencePrefixPolicy};
    let fence = FenceBoundary {
        opener: FenceOpener {
            line: 0,
            marker: 0..3,
            marker_width: 3,
        },
        prefix_policy: FencePrefixPolicy::ActivePrefixQuote { depth: 1, base: 0 },
        close_column: 0,
    };
    let source = "{ 💥\r\n> ```\nouter";
    let (green, records, exit, suffix) = parse(source, 100, Some(&fence), None);
    assert_eq!(green.to_string(), "{ 💥");
    assert_eq!(
        records,
        [
            record(
                0,
                GrammarRole::BracedStatementBlock(BracedStatementBlockRole::Statement),
                102..106,
                true
            ),
            record(
                1,
                GrammarRole::ClosingDelimiter {
                    owner: ConstructRole::BracedStatementBlockExpression,
                    delimiter: Delimiter::Brace
                },
                108..108,
                false
            )
        ]
    );
    assert!(matches!(
        exit,
        NormalizedExit::Complete(Err(Either::Left(_)), _)
    ));
    assert_eq!(suffix, "> ```\nouter");
    let (again, frozen, _, _) = parse(source, 100, Some(&fence), Some(&records));
    assert_eq!(again, green);
    assert_eq!(frozen, records);
    let (green, records, _, _) = parse("{ @\n@ x}", 0, None, None);
    assert_eq!(green.to_string(), "{ @\n@ x}");
    assert_eq!(
        records,
        [
            record(
                0,
                GrammarRole::BracedStatementBlock(BracedStatementBlockRole::Statement),
                2..3,
                true
            ),
            record(
                1,
                GrammarRole::BracedStatementBlock(BracedStatementBlockRole::Statement),
                4..5,
                true
            )
        ]
    );
}

#[test]
fn optional_statement_rejection_is_effect_free() {
    let (green, records, exit, suffix) = parse("@ rest", 0, None, None);
    assert_eq!(green.to_string(), "");
    assert!(records.is_empty());
    assert!(matches!(
        exit,
        NormalizedExit::Complete(Err(Either::Left(_)), _)
    ));
    assert_eq!(suffix, " rest");
}
