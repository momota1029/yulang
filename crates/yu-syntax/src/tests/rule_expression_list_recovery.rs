use crate::tests::support::*;
use crate::{
    recovery_record::{
        ConstructRole, Delimiter, DiagnosticId, ExpectationSources, ExpectedSyntax,
        ExpressionListRole, GrammarRole, PunctuationEvidence, RecoveryKind, RecoverySiteKey,
        SyntaxExpectation, UnexpectedCategory, UnexpectedSyntax,
    },
    rule::{rule_body_witness, scan_rule_current_item_witness, scan_rule_item_witness},
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
    let (green, records, _) = parse_with_fence_remainder(source, origin, frozen, fence);
    (green, records)
}

fn parse_with_fence_remainder(
    source: &str,
    origin: usize,
    frozen: Option<&[CommittedRecoveryRecord]>,
    fence: Option<&FenceBoundary>,
) -> (GreenNode, Vec<CommittedRecoveryRecord>, String) {
    let operators = OperatorTable::empty();
    let mut recover = Recover::new_for_test(&operators);
    let mut input = source;
    let mut output = frozen
        .map(|records| {
            recover = Recover::reconcile_for_test(recover.operators(), records);
            GreenNodeBuilder::new()
        })
        .unwrap_or_else(GreenNodeBuilder::new);
    output.start_node(SyntaxKind::Root.into());
    let opener = scan_rule_item_witness(chasa_recover::In::new(
        &mut input,
        &mut crate::cursor::LexRecover::new_for_test(recover.operators()),
        (),
    ))
    .unwrap();
    let current = scan_rule_current_item_witness(
        chasa_recover::In::new(
            &mut input,
            &mut crate::cursor::LexRecover::new_for_test(recover.operators()),
            (),
        ),
        origin + 1,
        LineEntry::InLine,
        fence,
    );
    let end = origin + source.len() - input.len();
    rule_body_witness(
        crate::cursor::SyntaxIn::new(&mut input, &mut recover, &mut output),
        opener,
        current.item,
        current.next_line_entry,
        end,
        fence,
    );
    output.finish_node();
    (
        output.finish(),
        recover.finish_recoveries_for_test(),
        input.to_owned(),
    )
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

fn direct_kinds(node: &SyntaxNode) -> Vec<SyntaxKind> {
    node.children_with_tokens()
        .map(|child| child.kind())
        .collect()
}

fn only_node(root: &SyntaxNode, kind: SyntaxKind) -> SyntaxNode {
    root.descendants()
        .find(|node| node.kind() == kind)
        .unwrap_or_else(|| panic!("expected {kind:?}"))
}

fn direct_token_range(parent: &SyntaxNode, kind: SyntaxKind) -> rowan::TextRange {
    parent
        .children_with_tokens()
        .find_map(|child| child.into_token().filter(|token| token.kind() == kind))
        .unwrap_or_else(|| panic!("expected direct {kind:?} token"))
        .text_range()
}

#[test]
fn direct_rowan_expression_list_phases_distinguish_every_rule_caller() {
    for (source, caller, open, close, range) in [
        (
            "{[1,2]}",
            SyntaxKind::RuleItem,
            SyntaxKind::LBracket,
            SyntaxKind::RBracket,
            1..6,
        ),
        (
            "{a(1,2)}",
            SyntaxKind::RuleCall,
            SyntaxKind::LParen,
            SyntaxKind::RParen,
            2..7,
        ),
        (
            "{a[1,2]}",
            SyntaxKind::RuleIndex,
            SyntaxKind::LBracket,
            SyntaxKind::RBracket,
            2..7,
        ),
    ] {
        let (green, records) = parse(source, 0, None);
        assert!(records.is_empty(), "{source:?}");
        let caller = only_node(&SyntaxNode::new_root(green), caller);
        assert_eq!(
            caller.text_range(),
            rowan::TextRange::new(range.start.into(), range.end.into())
        );
        let children = direct_kinds(&caller);
        assert_eq!(children.first(), Some(&open), "{source:?}");
        assert_eq!(children.last(), Some(&close), "{source:?}");
        assert_eq!(
            direct_token_range(&caller, open),
            rowan::TextRange::new(range.start.into(), (range.start + 1).into())
        );
        assert_eq!(
            direct_token_range(&caller, close),
            rowan::TextRange::new((range.end - 1).into(), range.end.into())
        );
        assert_eq!(
            children
                .iter()
                .filter(|kind| **kind == SyntaxKind::Comma)
                .count(),
            1
        );
        assert_eq!(
            children
                .iter()
                .filter(|kind| **kind == SyntaxKind::OperatorChain)
                .count(),
            2,
            "{source:?}"
        );
        let expressions = caller
            .children()
            .filter(|node| node.kind() == SyntaxKind::OperatorChain)
            .collect::<Vec<_>>();
        assert_eq!(
            expressions[0].text_range(),
            rowan::TextRange::new((range.start + 1).into(), (range.start + 2).into())
        );
        assert_eq!(
            expressions[1].text_range(),
            rowan::TextRange::new((range.end - 2).into(), (range.end - 1).into())
        );
    }
}

#[test]
fn direct_rowan_expression_list_accepts_empty_and_trailing_contents() {
    for (source, caller, open, close, trailing) in [
        (
            "{[]}",
            SyntaxKind::RuleItem,
            SyntaxKind::LBracket,
            SyntaxKind::RBracket,
            false,
        ),
        (
            "{a()}",
            SyntaxKind::RuleCall,
            SyntaxKind::LParen,
            SyntaxKind::RParen,
            false,
        ),
        (
            "{a[]}",
            SyntaxKind::RuleIndex,
            SyntaxKind::LBracket,
            SyntaxKind::RBracket,
            false,
        ),
        (
            "{[1,]}",
            SyntaxKind::RuleItem,
            SyntaxKind::LBracket,
            SyntaxKind::RBracket,
            true,
        ),
        (
            "{a(1,)}",
            SyntaxKind::RuleCall,
            SyntaxKind::LParen,
            SyntaxKind::RParen,
            true,
        ),
        (
            "{a[1,]}",
            SyntaxKind::RuleIndex,
            SyntaxKind::LBracket,
            SyntaxKind::RBracket,
            true,
        ),
    ] {
        let (green, records) = parse(source, 0, None);
        assert!(records.is_empty(), "{source:?}");
        let caller = only_node(&SyntaxNode::new_root(green), caller);
        let children = direct_kinds(&caller);
        assert_eq!(children.first(), Some(&open), "{source:?}");
        assert_eq!(children.last(), Some(&close), "{source:?}");
        assert_eq!(
            children
                .iter()
                .filter(|kind| **kind == SyntaxKind::Missing)
                .count(),
            0,
            "{source:?}"
        );
        assert_eq!(
            children
                .iter()
                .filter(|kind| **kind == SyntaxKind::Comma)
                .count(),
            usize::from(trailing),
            "{source:?}"
        );
    }
}

#[test]
fn direct_rowan_expression_list_recovery_has_phase_order_and_caller_paths() {
    let (green, _) = parse("{a(@x)}", 0, None);
    let call = only_node(&SyntaxNode::new_root(green), SyntaxKind::RuleCall);
    assert_eq!(
        direct_kinds(&call),
        [
            SyntaxKind::LParen,
            SyntaxKind::Error,
            SyntaxKind::OperatorChain,
            SyntaxKind::RParen,
        ]
    );
    assert_eq!(
        direct_token_range(&call, SyntaxKind::Error),
        rowan::TextRange::new(3.into(), 4.into())
    );

    let (green, _) = parse("{a(1;)}", 0, None);
    let call = only_node(&SyntaxNode::new_root(green), SyntaxKind::RuleCall);
    assert_eq!(
        direct_kinds(&call),
        [
            SyntaxKind::LParen,
            SyntaxKind::OperatorChain,
            SyntaxKind::Error,
            SyntaxKind::RParen,
        ]
    );
    assert_eq!(
        direct_token_range(&call, SyntaxKind::Error),
        rowan::TextRange::new(4.into(), 5.into())
    );

    let (green, _) = parse("{a(1;,x)}", 0, None);
    let call = only_node(&SyntaxNode::new_root(green), SyntaxKind::RuleCall);
    assert_eq!(
        direct_kinds(&call),
        [
            SyntaxKind::LParen,
            SyntaxKind::OperatorChain,
            SyntaxKind::Error,
            SyntaxKind::Comma,
            SyntaxKind::OperatorChain,
            SyntaxKind::RParen,
        ]
    );
    assert_eq!(
        direct_token_range(&call, SyntaxKind::Error),
        rowan::TextRange::new(4.into(), 5.into())
    );

    let (green, _) = parse("{a(@)}", 0, None);
    let call = only_node(&SyntaxNode::new_root(green), SyntaxKind::RuleCall);
    assert_eq!(
        direct_kinds(&call),
        [
            SyntaxKind::LParen,
            SyntaxKind::Error,
            SyntaxKind::Missing,
            SyntaxKind::RParen,
        ]
    );
    assert_eq!(
        direct_token_range(&call, SyntaxKind::Error),
        rowan::TextRange::new(3.into(), 4.into())
    );
    assert_eq!(
        only_node(&call, SyntaxKind::Missing).text_range(),
        rowan::TextRange::empty(4.into())
    );

    for (source, caller, missing_at) in [
        ("{a(,)}", SyntaxKind::RuleCall, 3),
        ("{[1}", SyntaxKind::RuleItem, 3),
        ("{a[1}", SyntaxKind::RuleIndex, 4),
    ] {
        let (green, _) = parse(source, 0, None);
        let caller = only_node(&SyntaxNode::new_root(green), caller);
        let missing = only_node(&caller, SyntaxKind::Missing);
        assert_eq!(
            missing.text_range(),
            rowan::TextRange::empty(missing_at.into())
        );
        assert_eq!(missing.parent(), Some(caller), "{source:?}");
    }
}

#[test]
fn direct_rowan_expression_list_newline_and_handoff_controls() {
    for (source, missing_at, newline) in [("{a(1\n\n2)}", 5, "\n"), ("{a(1\r\n\r\n2)}", 6, "\r\n")]
    {
        let (green, _) = parse(source, 0, None);
        let call = only_node(&SyntaxNode::new_root(green), SyntaxKind::RuleCall);
        let children = call.children_with_tokens().collect::<Vec<_>>();
        let missing_index = children
            .iter()
            .position(|child| child.kind() == SyntaxKind::Missing)
            .expect("newline-required Item Missing");
        let following_newline = children[missing_index + 1]
            .clone()
            .into_token()
            .expect("Missing precedes direct newline");
        assert_eq!(following_newline.kind(), SyntaxKind::Newline);
        assert_eq!(following_newline.text(), newline);
        assert_eq!(
            following_newline.text_range(),
            rowan::TextRange::new(
                missing_at.into(),
                (missing_at + newline.len() as u32).into()
            )
        );
        let missing = children[missing_index].as_node().expect("Missing node");
        assert_eq!(
            missing.text_range(),
            rowan::TextRange::empty(missing_at.into())
        );
    }

    let (green, _) = parse("{a(1]}", 0, None);
    let call = only_node(&SyntaxNode::new_root(green), SyntaxKind::RuleCall);
    assert_eq!(direct_kinds(&call).last(), Some(&SyntaxKind::Missing));
    assert_eq!(
        only_node(&call, SyntaxKind::Missing).text_range(),
        rowan::TextRange::empty(4.into())
    );

    let (green, _) = parse("{a(1", 0, None);
    let call = only_node(&SyntaxNode::new_root(green), SyntaxKind::RuleCall);
    assert_eq!(
        direct_kinds(&call),
        [
            SyntaxKind::LParen,
            SyntaxKind::OperatorChain,
            SyntaxKind::Missing
        ]
    );
    let missing = only_node(&call, SyntaxKind::Missing);
    assert_eq!(missing.parent(), Some(call.clone()));
    assert_eq!(missing.text_range(), rowan::TextRange::empty(4.into()));

    let (green, _) = parse("{a(x.)}", 0, None);
    let call = only_node(&SyntaxNode::new_root(green), SyntaxKind::RuleCall);
    let expression = only_node(&call, SyntaxKind::OperatorChain);
    assert!(
        expression
            .descendants()
            .any(|node| node.kind() == SyntaxKind::Missing)
    );
    assert!(
        !call
            .children()
            .any(|node| node.kind() == SyntaxKind::Missing)
    );

    let (green, _) = parse("{a(1).x}", 0, None);
    let root = SyntaxNode::new_root(green);
    let call = only_node(&root, SyntaxKind::RuleCall);
    let field = only_node(&root, SyntaxKind::RuleField);
    assert_eq!(field.parent(), call.parent());
    assert!(
        !call
            .descendants()
            .any(|node| node.kind() == SyntaxKind::RuleField)
    );
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
        GrammarRole::Expression(crate::recovery_record::ExpressionRole::FieldName)
    );
    assert_eq!(records[0].site.range, 5..5);
    assert_eq!(records[0].kind, RecoveryKind::Missing);
}

#[test]
fn fenced_repeated_newlines_use_physical_end_coordinates_and_frozen_records() {
    use crate::lexical::yumark::{FenceOpener, FencePrefixPolicy};
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
    use crate::{
        lexical::{
            expression_item::expression_item,
            yumark::{FenceOpener, FencePrefixPolicy},
        },
        rule::{RuleWitnessExit, expression_list_handoff_witness},
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
        let mut recover = Recover::new_for_test(&operators);
        let mut input = source;
        let mut output = GreenNodeBuilder::new();
        output.start_node(SyntaxKind::Root.into());
        let (item, origin, _) = expression_item(
            crate::cursor::SyntaxIn::new(&mut input, &mut recover, &mut output),
            OperatorSite::Nud,
            100,
            LineEntry::InLine,
            fenced.then_some(&fence),
            0,
            0,
        );
        let mut expected_input = source;
        let (original, _, _) = expression_item(
            crate::cursor::SyntaxIn::new(&mut expected_input, &mut recover, &mut output),
            OperatorSite::Nud,
            100,
            LineEntry::InLine,
            fenced.then_some(&fence),
            0,
            0,
        );
        let suffix = input.to_owned();
        let exit = expression_list_handoff_witness(
            crate::cursor::SyntaxIn::new(&mut input, &mut recover, &mut output),
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
        let (green, records) = (output.finish(), recover.finish_recoveries_for_test());
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

#[test]
fn direct_rowan_expression_list_recovery_is_proven_per_caller_phase() {
    for (source, caller_kind, open, close, error_range) in [
        (
            "{[@x]}",
            SyntaxKind::RuleItem,
            SyntaxKind::LBracket,
            SyntaxKind::RBracket,
            2..3,
        ),
        (
            "{a(@x)}",
            SyntaxKind::RuleCall,
            SyntaxKind::LParen,
            SyntaxKind::RParen,
            3..4,
        ),
        (
            "{a[@x]}",
            SyntaxKind::RuleIndex,
            SyntaxKind::LBracket,
            SyntaxKind::RBracket,
            3..4,
        ),
    ] {
        let (green, _) = parse(source, 0, None);
        let caller = only_node(&SyntaxNode::new_root(green), caller_kind);
        assert_eq!(
            direct_kinds(&caller),
            [open, SyntaxKind::Error, SyntaxKind::OperatorChain, close]
        );
        assert_eq!(
            direct_token_range(&caller, SyntaxKind::Error),
            rowan::TextRange::new(error_range.start.into(), error_range.end.into())
        );
    }
    for (source, caller_kind, open, close, error_range) in [
        (
            "{[1;]}",
            SyntaxKind::RuleItem,
            SyntaxKind::LBracket,
            SyntaxKind::RBracket,
            3..4,
        ),
        (
            "{a(1;)}",
            SyntaxKind::RuleCall,
            SyntaxKind::LParen,
            SyntaxKind::RParen,
            4..5,
        ),
        (
            "{a[1;]}",
            SyntaxKind::RuleIndex,
            SyntaxKind::LBracket,
            SyntaxKind::RBracket,
            4..5,
        ),
    ] {
        let (green, _) = parse(source, 0, None);
        let caller = only_node(&SyntaxNode::new_root(green), caller_kind);
        assert_eq!(
            direct_kinds(&caller),
            [open, SyntaxKind::OperatorChain, SyntaxKind::Error, close]
        );
        assert_eq!(
            direct_token_range(&caller, SyntaxKind::Error),
            rowan::TextRange::new(error_range.start.into(), error_range.end.into())
        );
    }
    for (source, caller_kind, open, close, error_range) in [
        (
            "{[1;,x]}",
            SyntaxKind::RuleItem,
            SyntaxKind::LBracket,
            SyntaxKind::RBracket,
            3..4,
        ),
        (
            "{a(1;,x)}",
            SyntaxKind::RuleCall,
            SyntaxKind::LParen,
            SyntaxKind::RParen,
            4..5,
        ),
        (
            "{a[1;,x]}",
            SyntaxKind::RuleIndex,
            SyntaxKind::LBracket,
            SyntaxKind::RBracket,
            4..5,
        ),
    ] {
        let (green, _) = parse(source, 0, None);
        let caller = only_node(&SyntaxNode::new_root(green), caller_kind);
        assert_eq!(
            direct_kinds(&caller),
            [
                open,
                SyntaxKind::OperatorChain,
                SyntaxKind::Error,
                SyntaxKind::Comma,
                SyntaxKind::OperatorChain,
                close
            ]
        );
        assert_eq!(
            direct_token_range(&caller, SyntaxKind::Error),
            rowan::TextRange::new(error_range.start.into(), error_range.end.into())
        );
    }
}

#[test]
fn direct_rowan_expression_list_terminal_item_suffixes_are_caller_specific() {
    for (source, caller_kind, open, missing_at) in [
        ("{[@", SyntaxKind::RuleItem, SyntaxKind::LBracket, 3),
        ("{a(@", SyntaxKind::RuleCall, SyntaxKind::LParen, 4),
        ("{a[@", SyntaxKind::RuleIndex, SyntaxKind::LBracket, 4),
        ("{[@)}", SyntaxKind::RuleItem, SyntaxKind::LBracket, 3),
        ("{a(@]}", SyntaxKind::RuleCall, SyntaxKind::LParen, 4),
        ("{a[@)}", SyntaxKind::RuleIndex, SyntaxKind::LBracket, 4),
    ] {
        let (green, _) = parse(source, 0, None);
        let caller = only_node(&SyntaxNode::new_root(green), caller_kind);
        assert_eq!(
            direct_kinds(&caller),
            [
                open,
                SyntaxKind::Error,
                SyntaxKind::Missing,
                SyntaxKind::Missing
            ]
        );
        let missings = caller
            .children()
            .filter(|node| node.kind() == SyntaxKind::Missing)
            .collect::<Vec<_>>();
        assert_eq!(missings.len(), 2);
        assert!(
            missings
                .iter()
                .all(|node| node.text_range() == rowan::TextRange::empty(missing_at.into()))
        );
    }
    for (source, caller_kind, open, close, missing_at) in [
        (
            "{[@]}",
            SyntaxKind::RuleItem,
            SyntaxKind::LBracket,
            SyntaxKind::RBracket,
            3,
        ),
        (
            "{a(@)}",
            SyntaxKind::RuleCall,
            SyntaxKind::LParen,
            SyntaxKind::RParen,
            4,
        ),
        (
            "{a[@]}",
            SyntaxKind::RuleIndex,
            SyntaxKind::LBracket,
            SyntaxKind::RBracket,
            4,
        ),
    ] {
        let (green, _) = parse(source, 0, None);
        let caller = only_node(&SyntaxNode::new_root(green), caller_kind);
        assert_eq!(
            direct_kinds(&caller),
            [open, SyntaxKind::Error, SyntaxKind::Missing, close]
        );
        assert_eq!(
            only_node(&caller, SyntaxKind::Missing).text_range(),
            rowan::TextRange::empty(missing_at.into())
        );
    }
}

#[test]
fn direct_rowan_expression_list_newline_missing_ranges_cover_all_callers() {
    for (source, caller_kind, missing_at, newline) in [
        ("{[1\n\n2]}", SyntaxKind::RuleItem, 4, "\n"),
        ("{a(1\n\n2)}", SyntaxKind::RuleCall, 5, "\n"),
        ("{a[1\n\n2]}", SyntaxKind::RuleIndex, 5, "\n"),
        ("{[1\r\n\r\n2]}", SyntaxKind::RuleItem, 5, "\r\n"),
        ("{a(1\r\n\r\n2)}", SyntaxKind::RuleCall, 6, "\r\n"),
        ("{a[1\r\n\r\n2]}", SyntaxKind::RuleIndex, 6, "\r\n"),
    ] {
        let (green, _) = parse(source, 0, None);
        let caller = only_node(&SyntaxNode::new_root(green), caller_kind);
        let children = caller.children_with_tokens().collect::<Vec<_>>();
        let missing_index = children
            .iter()
            .position(|child| child.kind() == SyntaxKind::Missing)
            .expect("newline-required Item Missing");
        assert_eq!(
            children[missing_index].as_node().unwrap().text_range(),
            rowan::TextRange::empty(missing_at.into())
        );
        let newline_token = children[missing_index + 1]
            .clone()
            .into_token()
            .expect("Missing precedes direct newline");
        assert_eq!(newline_token.kind(), SyntaxKind::Newline);
        assert_eq!(newline_token.text(), newline);
        assert_eq!(
            newline_token.text_range(),
            rowan::TextRange::new(
                missing_at.into(),
                (missing_at + newline.len() as u32).into()
            )
        );
    }
}

#[test]
fn direct_rowan_expression_list_fence_handoff_is_caller_owned_but_not_a_complete_tree() {
    use crate::lexical::yumark::{FenceOpener, FencePrefixPolicy};
    let fence = FenceBoundary {
        opener: FenceOpener {
            line: 0,
            marker: 0..3,
            marker_width: 3,
        },
        prefix_policy: FencePrefixPolicy::ActivePrefixQuote { depth: 1, base: 0 },
        close_column: 0,
    };
    for (source, caller_kind, open, prefix, missing_at) in [
        (
            "{[\r\n> ```\nouter",
            SyntaxKind::RuleItem,
            SyntaxKind::LBracket,
            "{[",
            2,
        ),
        (
            "{a(\r\n> ```\nouter",
            SyntaxKind::RuleCall,
            SyntaxKind::LParen,
            "{a(",
            3,
        ),
        (
            "{a[\r\n> ```\nouter",
            SyntaxKind::RuleIndex,
            SyntaxKind::LBracket,
            "{a[",
            3,
        ),
    ] {
        let (green, _, remainder) = parse_with_fence_remainder(source, 100, None, Some(&fence));
        assert_eq!(
            green.to_string(),
            prefix,
            "the witness builder stops before the protected Item"
        );
        assert_eq!(
            remainder, "> ```\nouter",
            "the witness exposes the pending fence Item after its preceding boundary newline"
        );
        let caller = only_node(&SyntaxNode::new_root(green), caller_kind);
        assert_eq!(direct_kinds(&caller), [open, SyntaxKind::Missing]);
        assert_eq!(
            only_node(&caller, SyntaxKind::Missing).text_range(),
            rowan::TextRange::empty(missing_at.into())
        );
    }
}

#[test]
fn direct_rowan_expression_list_error_leaves_preserve_present_boundaries() {
    let (green, _) = parse("{a(@ @x)}", 0, None);
    let call = only_node(&SyntaxNode::new_root(green), SyntaxKind::RuleCall);
    assert_eq!(
        direct_kinds(&call),
        [
            SyntaxKind::LParen,
            SyntaxKind::Error,
            SyntaxKind::Error,
            SyntaxKind::Error,
            SyntaxKind::OperatorChain,
            SyntaxKind::RParen
        ]
    );
    let errors = call
        .children_with_tokens()
        .filter_map(|child| {
            child
                .into_token()
                .filter(|token| token.kind() == SyntaxKind::Error)
        })
        .collect::<Vec<_>>();
    assert_eq!(
        errors.iter().map(|token| token.text()).collect::<Vec<_>>(),
        ["@", " ", "@"]
    );
    assert_eq!(
        errors
            .iter()
            .map(|token| token.text_range())
            .collect::<Vec<_>>(),
        [
            rowan::TextRange::new(3.into(), 4.into()),
            rowan::TextRange::new(4.into(), 5.into()),
            rowan::TextRange::new(5.into(), 6.into())
        ]
    );
}
