use crate::tests::support::*;
use crate::{
    rule::{
        RuleWitnessExit, rule_body_normalized_witness, scan_rule_current_item_witness,
        scan_rule_item_witness,
    },
    structural_diagnostic::StructuralKind,
};

fn parse(source: &str, origin: usize) -> GreenNode {
    parse_with_fence(source, origin, None)
}

fn parse_with_fence(source: &str, origin: usize, fence: Option<&FenceBoundary>) -> GreenNode {
    let (green, _) = parse_with_fence_remainder(source, origin, fence);
    green
}

fn parse_with_fence_remainder(
    source: &str,
    origin: usize,
    fence: Option<&FenceBoundary>,
) -> (GreenNode, String) {
    let (green, remainder, _, _) = parse_with_fence_handoff(source, origin, fence);
    (green, remainder)
}

fn parse_with_fence_handoff(
    source: &str,
    origin: usize,
    fence: Option<&FenceBoundary>,
) -> (GreenNode, String, RuleWitnessExit, LineEntry) {
    let operators = OperatorTable::empty();
    let mut recover = Recover::new_for_test(&operators);
    let mut input = source;
    let mut output = GreenNodeBuilder::new();
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
    let (exit, line_entry) = rule_body_normalized_witness(
        crate::cursor::SyntaxIn::new(&mut input, &mut recover, &mut output),
        opener,
        current.item,
        current.next_line_entry,
        end,
        fence,
    );
    output.finish_node();
    (
        finish_with_discarded_recoveries(output, recover),
        input.to_owned(),
        exit,
        line_entry,
    )
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
        let green = parse(source, 0);
        assert!(structural_facts(&green).is_empty(), "{source:?}");
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
        let green = parse(source, 0);
        assert!(structural_facts(&green).is_empty(), "{source:?}");
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
    let green = parse("{a(@x)}", 0);
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

    let green = parse("{a(1;)}", 0);
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

    let green = parse("{a(1;,x)}", 0);
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

    let green = parse("{a(@)}", 0);
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
        let green = parse(source, 0);
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
        let green = parse(source, 0);
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

    let green = parse("{a(1]}", 0);
    let call = only_node(&SyntaxNode::new_root(green), SyntaxKind::RuleCall);
    assert_eq!(direct_kinds(&call).last(), Some(&SyntaxKind::Missing));
    assert_eq!(
        only_node(&call, SyntaxKind::Missing).text_range(),
        rowan::TextRange::empty(4.into())
    );

    let green = parse("{a(1", 0);
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

    let green = parse("{a(x.)}", 0);
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

    let green = parse("{a(1).x}", 0);
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
fn list_slots_have_exact_structural_facts_in_all_callers() {
    for (source, expected) in [
        ("{[,]}", vec![(StructuralKind::Missing, 2..2)]),
        ("{a[,]}", vec![(StructuralKind::Missing, 3..3)]),
        ("{a(,)}", vec![(StructuralKind::Missing, 3..3)]),
        ("{a(@@x)}", vec![(StructuralKind::ErrorGroup, 3..5)]),
        (
            "{a(@)}",
            vec![
                (StructuralKind::ErrorGroup, 3..4),
                (StructuralKind::Missing, 4..4),
            ],
        ),
        ("{a(α;)}", vec![(StructuralKind::ErrorGroup, 5..6)]),
        (
            "{a(1\r\n\r\n\n2)}",
            vec![
                (StructuralKind::Missing, 6..6),
                (StructuralKind::Missing, 8..8),
            ],
        ),
        ("{a(1}", vec![(StructuralKind::Missing, 4..4)]),
        ("{a[1}", vec![(StructuralKind::Missing, 4..4)]),
    ] {
        for origin in [0, 137] {
            let green = parse(source, origin);
            assert_eq!(green.to_string(), source);
            assert_eq!(structural_facts(&green), expected, "{source:?} at {origin}");
        }
    }
}

#[test]
fn accepted_empty_and_trailing_separators_remain_structural_fact_free() {
    for source in ["{[] a() a[]}", "{[α,] a(1,) a[1,]}", "{a(1\r\n)}"] {
        let green = parse(source, 0);
        assert_eq!(green.to_string(), source);
        assert!(structural_facts(&green).is_empty(), "{source:?}");
    }
}

#[test]
fn nested_expression_recovery_has_its_child_structural_fact() {
    let green = parse("{a(x.)}", 0);
    assert_eq!(green.to_string(), "{a(x.)}");
    assert_eq!(structural_facts(&green), [(StructuralKind::Missing, 5..5)]);
}

#[test]
fn nested_field_missing_has_one_cst_occurrence_in_every_rule_list_caller() {
    use SyntaxKind::*;

    let range = |node: &SyntaxNode| {
        usize::from(node.text_range().start())..usize::from(node.text_range().end())
    };
    for (source, caller_kind, open, close, at) in [
        ("{[x.]}", RuleItem, LBracket, RBracket, 4),
        ("{a(x.)}", RuleCall, LParen, RParen, 5),
        ("{a[x.]}", RuleIndex, LBracket, RBracket, 5),
    ] {
        let (green, remainder, exit, line_entry) = parse_with_fence_handoff(source, 0, None);
        let root = SyntaxNode::new_root(green.clone());
        let end = source.len();
        let separate_caller = caller_kind != RuleItem;
        let caller_index = if separate_caller { 5 } else { 4 };
        let chain_index = caller_index + 1;
        let field_index = chain_index + 2;
        let mut expected_nodes = vec![
            (Root, 0..end, None, vec![RuleBody]),
            (
                RuleBody,
                0..end,
                Some(0),
                vec![LBrace, RuleAlternation, RBrace],
            ),
            (RuleAlternation, 1..end - 1, Some(1), vec![RuleSequence]),
            (RuleSequence, 1..end - 1, Some(2), vec![RuleItem]),
        ];
        if separate_caller {
            expected_nodes.push((RuleItem, 1..end - 1, Some(3), vec![Identifier, caller_kind]));
        }
        expected_nodes.extend([
            (
                caller_kind,
                at - 3..at + 1,
                Some(if separate_caller { 4 } else { 3 }),
                vec![open, OperatorChain, close],
            ),
            (
                OperatorChain,
                at - 2..at,
                Some(caller_index),
                vec![IdentifierExpression, FieldTail],
            ),
            (
                IdentifierExpression,
                at - 2..at - 1,
                Some(chain_index),
                vec![Identifier],
            ),
            (FieldTail, at - 1..at, Some(chain_index), vec![Dot, Missing]),
            (Missing, at..at, Some(field_index), vec![]),
        ]);
        let nodes = root.descendants().collect::<Vec<_>>();
        assert_eq!(nodes.len(), expected_nodes.len(), "{source:?}");
        for (node, (kind, span, parent, children)) in nodes.iter().zip(expected_nodes) {
            assert_eq!(node.kind(), kind, "{source:?}");
            assert_eq!(range(node), span, "{source:?}");
            assert_eq!(node.to_string(), &source[span]);
            assert_eq!(node.parent(), parent.map(|index| nodes[index].clone()));
            assert_eq!(direct_kinds(node), children, "{source:?}");
        }
        let mut expected_tokens = vec![(LBrace, 0..1, 1)];
        if separate_caller {
            expected_tokens.push((Identifier, 1..2, 4));
        }
        expected_tokens.extend([
            (open, at - 3..at - 2, caller_index),
            (Identifier, at - 2..at - 1, chain_index + 1),
            (Dot, at - 1..at, field_index),
            (close, at..at + 1, caller_index),
            (RBrace, at + 1..end, 1),
        ]);
        let tokens = root
            .descendants_with_tokens()
            .filter_map(|element| element.into_token())
            .collect::<Vec<_>>();
        assert_eq!(tokens.len(), expected_tokens.len(), "{source:?}");
        for (token, (kind, span, parent)) in tokens.iter().zip(expected_tokens) {
            assert_eq!(token.kind(), kind);
            assert_eq!(
                usize::from(token.text_range().start())..usize::from(token.text_range().end()),
                span
            );
            assert_eq!(token.text(), &source[span]);
            assert_eq!(token.parent(), Some(nodes[parent].clone()));
        }
        let recovery = root
            .descendants_with_tokens()
            .filter(|element| matches!(element.kind(), Missing | Error | Invalid))
            .collect::<Vec<_>>();
        assert_eq!(recovery.len(), 1, "{source:?}");
        assert_eq!(recovery[0].as_node(), Some(&nodes[field_index + 1]));
        assert_eq!(
            structural_facts(&green),
            [(StructuralKind::Missing, at..at)]
        );
        assert_eq!(green.to_string(), source);
        assert!(remainder.is_empty());
        assert_eq!(exit, RuleWitnessExit::Complete);
        assert_eq!(line_entry, LineEntry::InLine);
    }
}

#[test]
fn fenced_repeated_newlines_use_physical_end_coordinates_and_structural_facts() {
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
    let green = parse_with_fence(source, 100, Some(&fence));
    assert_eq!(green.to_string(), source);
    assert_eq!(structural_facts(&green), [(StructuralKind::Missing, 8..8)]);
}

#[test]
fn protected_terminal_items_keep_all_leading_and_exact_close_handoff() {
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
    for (source, fenced) in [
        (" \r\n  ", false),
        (" \r\n  }", false),
        ("\r\n> ```\nouter", true),
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
        let green = finish_with_discarded_recoveries(output, recover);
        assert_eq!(green.to_string(), "");
        assert_eq!(
            structural_facts(&green),
            [(StructuralKind::Missing, 0..0)],
            "{source:?}"
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
        let green = parse(source, 0);
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
        let green = parse(source, 0);
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
        let green = parse(source, 0);
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
        let green = parse(source, 0);
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
        let green = parse(source, 0);
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
        let green = parse(source, 0);
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
    use crate::lexical::{
        item::{BorrowedTarget, Boundary, LeadingTrivia, Payload, PendingBoundary},
        yumark::{FenceCloseFacts, FenceOpener, FencePrefixPolicy, QuotePrefixFacts},
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
        let origin = 100;
        let (green, remainder, exit, line_entry) =
            parse_with_fence_handoff(source, origin, Some(&fence));
        let RuleWitnessExit::Returned(item) = exit else {
            panic!("the caller returns its protected fence Item")
        };
        assert_eq!(line_entry, LineEntry::PhysicalStart);
        let b = origin + prefix.len() + 2;
        let expected_boundary = PendingBoundary::new(
            b..b + 6,
            Boundary::BorrowedClose(BorrowedTarget::YumarkFence(Box::new(FenceCloseFacts {
                line: b,
                inspected: b..b + 6,
                prefix: Some(QuotePrefixFacts {
                    indentation: b..b,
                    marker: b..b + 1,
                    extent: b..b + 2,
                    depth: 1,
                    marker_len: 2,
                    marker_end: 1,
                    explicit: false,
                }),
                indentation: b + 2..b + 2,
                indentation_column: 0,
                marker: b + 2..b + 5,
                marker_width: 3,
                horizontal_suffix: b + 5..b + 5,
                newline: Some(b + 5..b + 6),
            }))),
        );
        let pending = item
            .payload_view()
            .pending_boundary()
            .expect("fence boundary");
        assert_eq!(pending.coordinate(), b);
        assert_eq!(pending.inspected(), &(b..b + 6));
        assert_eq!(pending, &expected_boundary);
        let extent = item.extent(b);
        assert_eq!(extent.physical(), origin + prefix.len()..b);
        assert_eq!(extent.leading(), origin + prefix.len()..b);
        assert_eq!(extent.remaining(), origin + prefix.len()..b);
        assert_eq!(extent.payload(), b..b);
        assert_eq!(
            item,
            Item::plain(
                LeadingTrivia::ordinary(
                    vec![ordinary_trivia(TriviaKind::Newline, "\r\n")].into_boxed_slice(),
                ),
                Payload::Boundary(expected_boundary.clone()),
            )
        );
        let (leading, pending) = emit_terminal_leading_text(item);
        assert_eq!(leading, "\r\n");
        assert_eq!(pending, expected_boundary);
        assert_eq!(format!("{green}{leading}{remainder}"), source);
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
fn direct_rowan_expression_list_fence_close_slots_have_native_caller_controls() {
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
    for (source, native, caller_kind, open, close, prefix, at) in [
        (
            "{[\r\n> ```\nouter",
            "{[]}",
            SyntaxKind::RuleItem,
            SyntaxKind::LBracket,
            SyntaxKind::RBracket,
            "{[",
            2u32,
        ),
        (
            "{a(\r\n> ```\nouter",
            "{a()}",
            SyntaxKind::RuleCall,
            SyntaxKind::LParen,
            SyntaxKind::RParen,
            "{a(",
            3,
        ),
        (
            "{a[\r\n> ```\nouter",
            "{a[]}",
            SyntaxKind::RuleIndex,
            SyntaxKind::LBracket,
            SyntaxKind::RBracket,
            "{a[",
            3,
        ),
    ] {
        for (input, fenced) in [(source, true), (native, false)] {
            let (green, remainder) = parse_with_fence_remainder(input, 0, fenced.then_some(&fence));
            assert_eq!(green.to_string(), if fenced { prefix } else { native });
            assert_eq!(remainder, if fenced { "> ```\nouter" } else { "" });
            let root = SyntaxNode::new_root(green);
            let caller = only_node(&root, caller_kind);
            let mut ancestry = vec![caller_kind];
            if caller_kind != SyntaxKind::RuleItem {
                ancestry.push(SyntaxKind::RuleItem);
            }
            ancestry.extend([
                SyntaxKind::RuleSequence,
                SyntaxKind::RuleAlternation,
                SyntaxKind::RuleBody,
                SyntaxKind::Root,
            ]);
            assert_eq!(
                caller
                    .ancestors()
                    .map(|node| node.kind())
                    .collect::<Vec<_>>(),
                ancestry,
                "{input:?}"
            );
            assert_eq!(
                direct_token_range(&caller, open),
                rowan::TextRange::new((at - 1).into(), at.into())
            );
            assert_eq!(
                direct_kinds(&caller),
                [open, if fenced { SyntaxKind::Missing } else { close }]
            );
            if fenced {
                // The final direct slot after this caller's opener expects its
                // matching close; the native control supplies that same slot.
                let missing = only_node(&caller, SyntaxKind::Missing);
                assert_eq!(missing.parent(), Some(caller.clone()));
                assert_eq!(missing.text_range(), rowan::TextRange::empty(at.into()));
                assert!(missing.children_with_tokens().next().is_none());
            } else {
                assert_eq!(
                    direct_token_range(&caller, close),
                    rowan::TextRange::new(at.into(), (at + 1).into())
                );
            }
            assert!(!root.descendants_with_tokens().any(|element| matches!(
                element.kind(),
                SyntaxKind::Error | SyntaxKind::Invalid | SyntaxKind::Newline
            )));
        }
    }
}

#[test]
fn direct_rowan_expression_list_error_leaves_preserve_present_boundaries() {
    let green = parse("{a(@ @x)}", 0);
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
