use super::*;
use crate::{
    parser::rule::{rule_body_witness, scan_rule_current_item_witness, scan_rule_item_witness},
    session::{
        ConstructRole, Delimiter, DiagnosticId, ExpectationSources, ExpectedSyntax,
        ExpressionListRole, GrammarRole, PunctuationEvidence, RecoveryKind, RecoverySiteKey,
        SyntaxExpectation, UnexpectedCategory, UnexpectedSyntax,
    },
};
use std::{ops::Range, sync::Arc};

fn parse(
    source: &str,
    origin: usize,
    frozen: Option<&[CommittedRecoveryRecord]>,
) -> (GreenNode, Vec<CommittedRecoveryRecord>) {
    parse_with_fence(source, origin, frozen, None)
}

fn parse_with_fence(
    source: &str,
    origin: usize,
    frozen: Option<&[CommittedRecoveryRecord]>,
    fence: Option<&FenceBoundary>,
) -> (GreenNode, Vec<CommittedRecoveryRecord>) {
    let operators = OperatorTable::empty();
    let mut recover = Recover::new(&operators);
    let mut input = source;
    let mut output = frozen
        .map(GreenNodeBuilder::reconcile)
        .unwrap_or_else(GreenNodeBuilder::new);
    output.start_node(SyntaxKind::Root.into());
    let opener = scan_rule_item_witness(In::new(&mut input, &mut recover, ())).unwrap();
    let current = scan_rule_current_item_witness(
        In::new(&mut input, &mut recover, ()),
        origin + 1,
        LineEntry::InLine,
        fence,
    );
    let end = origin + source.len() - input.len();
    rule_body_witness(
        In::new(&mut input, &mut recover, &mut output),
        opener,
        current.item,
        current.next_line_entry,
        end,
        fence,
    );
    output.finish_node();
    output.finish_with_recoveries()
}

fn record(id: u32, role: GrammarRole, range: Range<usize>, error: bool) -> CommittedRecoveryRecord {
    let expected = match role {
        GrammarRole::ExpressionList(ExpressionListRole::Item) => ExpectedSyntax::Expression,
        GrammarRole::ExpressionList(ExpressionListRole::Separator) => {
            ExpectedSyntax::DelimitedSequenceSeparator
        }
        GrammarRole::ClosingDelimiter { delimiter, .. } => {
            ExpectedSyntax::Punctuation(PunctuationEvidence::Close(delimiter))
        }
        _ => unreachable!(),
    };
    CommittedRecoveryRecord {
        id: DiagnosticId(id),
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
fn list_slots_have_exact_shifted_and_frozen_records_in_all_callers() {
    let item = GrammarRole::ExpressionList(ExpressionListRole::Item);
    let separator = GrammarRole::ExpressionList(ExpressionListRole::Separator);
    let close = |delimiter| GrammarRole::ClosingDelimiter {
        owner: ConstructRole::ExpressionList,
        delimiter,
    };
    for (source, slots) in [
        ("{[,]}", vec![(item, 2..2, false)]),
        ("{a[,]}", vec![(item, 3..3, false)]),
        ("{a(,)}", vec![(item, 3..3, false)]),
        ("{a(@@x)}", vec![(item, 3..4, true), (item, 4..5, true)]),
        ("{a(@)}", vec![(item, 3..4, true), (item, 4..4, false)]),
        ("{a(α;)}", vec![(separator, 5..6, true)]),
        (
            "{a(1\r\n\r\n\n2)}",
            vec![(item, 8..8, false), (item, 9..9, false)],
        ),
        ("{a(1}", vec![(close(Delimiter::Parenthesis), 4..4, false)]),
        ("{a[1}", vec![(close(Delimiter::Bracket), 4..4, false)]),
    ] {
        for origin in [0, 137] {
            let expected: Vec<_> = slots
                .iter()
                .enumerate()
                .map(|(id, (role, range, error))| {
                    record(
                        id as u32,
                        *role,
                        origin + range.start..origin + range.end,
                        *error,
                    )
                })
                .collect();
            let (green, records) = parse(source, origin, None);
            assert_eq!(green.to_string(), source);
            assert_eq!(records, expected, "{source:?}");
            let (again, frozen) = parse(source, origin, Some(&records));
            assert_eq!(again, green);
            assert_eq!(frozen, records);
        }
    }
}

#[test]
fn accepted_empty_and_trailing_separators_remain_record_free() {
    for source in ["{[] a() a[]}", "{[α,] a(1,) a[1,]}", "{a(1\r\n)}"] {
        let (green, records) = parse(source, 0, None);
        assert_eq!(green.to_string(), source);
        assert!(records.is_empty(), "{source:?}: {records:?}");
    }
}

#[test]
fn nested_expression_recovery_keeps_its_child_role() {
    let (green, records) = parse("{a(x.)}", 0, None);
    assert_eq!(green.to_string(), "{a(x.)}");
    assert_eq!(records.len(), 1);
    assert_eq!(
        records[0].site.role,
        GrammarRole::Expression(crate::session::ExpressionRole::FieldName)
    );
    assert_eq!(records[0].site.range, 5..5);
    assert_eq!(records[0].kind, RecoveryKind::Missing);
}

#[test]
fn fenced_repeated_newlines_use_physical_end_coordinates_and_frozen_records() {
    use crate::parser::yumark::{FenceOpener, FencePrefixPolicy};
    let fence = FenceBoundary {
        opener: FenceOpener {
            line: 0,
            marker: 0..3,
            marker_width: 3,
        },
        prefix_policy: FencePrefixPolicy::ActivePrefixQuote { depth: 1, base: 0 },
        close_column: 0,
    };
    let source = "{a(1\r\n> \r\n> 2)}";
    let (green, records) = parse_with_fence(source, 100, None, Some(&fence));
    assert_eq!(green.to_string(), source);
    assert_eq!(
        records,
        [record(
            0,
            GrammarRole::ExpressionList(ExpressionListRole::Item),
            110..110,
            false
        )]
    );
    let (again, frozen) = parse_with_fence(source, 100, Some(&records), Some(&fence));
    assert_eq!(again, green);
    assert_eq!(frozen, records);
}

#[test]
fn protected_terminal_items_keep_all_leading_and_exact_close_records() {
    use crate::parser::{
        driver::expression_item,
        rule::{RuleWitnessExit, expression_list_handoff_witness},
        yumark::{FenceOpener, FencePrefixPolicy},
    };
    let fence = FenceBoundary {
        opener: FenceOpener {
            line: 0,
            marker: 0..3,
            marker_width: 3,
        },
        prefix_policy: FencePrefixPolicy::ActivePrefixQuote { depth: 1, base: 0 },
        close_column: 0,
    };
    for (source, fenced, at) in [
        (" \r\n  ", false, 105),
        (" \r\n  }", false, 100),
        ("\r\n> ```\nouter", true, 102),
    ] {
        let operators = OperatorTable::empty();
        let mut recover = Recover::new(&operators);
        let mut input = source;
        let mut output = GreenNodeBuilder::new();
        output.start_node(SyntaxKind::Root.into());
        let (item, origin, _) = expression_item(
            In::new(&mut input, &mut recover, &mut output),
            OperatorSite::Nud,
            100,
            LineEntry::InLine,
            fenced.then_some(&fence),
            0,
            0,
        );
        let mut expected_input = source;
        let (original, _, _) = expression_item(
            In::new(&mut expected_input, &mut recover, &mut output),
            OperatorSite::Nud,
            100,
            LineEntry::InLine,
            fenced.then_some(&fence),
            0,
            0,
        );
        let suffix = input.to_owned();
        let exit = expression_list_handoff_witness(
            In::new(&mut input, &mut recover, &mut output),
            item,
            TokenKind::RParen,
            origin,
        );
        let RuleWitnessExit::Returned(pending) = exit else {
            panic!("terminal remains pending")
        };
        assert_eq!(pending, original);
        assert_eq!(input, suffix);
        output.finish_node();
        let (green, records) = output.finish_with_recoveries();
        assert_eq!(green.to_string(), "");
        assert_eq!(
            records,
            [record(
                0,
                GrammarRole::ClosingDelimiter {
                    owner: ConstructRole::ExpressionList,
                    delimiter: Delimiter::Parenthesis
                },
                at..at,
                false
            )]
        );
    }
}
