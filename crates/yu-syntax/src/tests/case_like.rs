use crate::tests::support::*;
use crate::{ExpectedSyntax, structural_diagnostic::StructuralKind};
use crate::{ambient_claim::AmbientClaimView, handoff::MlMode, statement::StatementLineHandoff};
use std::ops::Range;

/// Test-only labels for slots independently located through the asserted CST
/// parent/child topology below. They carry no parser output or diagnostic data.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum CstSlot {
    Arm,
    Arrow,
    Block,
    Body,
    Guard,
    Handler,
    Pattern,
}

fn sequence_fact(_: u32, _: bool, at: usize) -> StructuralFact {
    (StructuralKind::Missing, at..at)
}

#[test]
fn case_sequence_missing_slots_are_exact_at_source_offsets() {
    for (source, separator, at) in [
        // WP-7 removed the row for 'n -> [tail] -> yes': with list literals every pattern start is also an expression start, so an unread pattern-only opener no longer exists (design memo WP-7).
        ("catch action { err -> recover", false, 29),
        ("catch x { n -> a,  ", false, 19),
    ] {
        for origin in [0, 8100] {
            let expected = if separator {
                vec![
                    arm_fact(0, CstSlot::Body, at..at, false, &[]),
                    sequence_fact(1, true, at),
                ]
            } else {
                vec![sequence_fact(0, false, at)]
            };
            let operators = OperatorTable::empty();
            let mut recover = Recover::new_for_test(&operators);
            let mut output = GreenNodeBuilder::new();
            output.start_node(SyntaxKind::Root.into());
            let (_, suffix) = parse_case_into(source, origin, None, &mut recover, &mut output);
            output.finish_node();
            let green = finish_with_discarded_recoveries(output, recover);
            assert_eq!(suffix, "", "{source:?}");
            assert_eq!(green.to_string(), source, "{source:?}");
            assert_eq!(structural_facts(&green), expected, "{source:?}");
        }
    }
}

#[test]
fn qualified_constructor_payloads_leave_the_case_arrow_to_the_arm() {
    for (pattern, body) in [
        ("opt::just fill", "fill"),
        ("std::data::list::list_view::leaf item", "item"),
        ("result::ok inner", "inner"),
    ] {
        let source = format!("case x:\n  {pattern} -> {body}");
        let green = run(&source).0;
        assert_eq!(green.to_string(), source, "{source:?}");
        assert!(structural_facts(&green).is_empty(), "{source:?}");
        let root = crate::SyntaxNode::new_root(green);
        let arm = root
            .descendants()
            .find(|node| node.kind() == crate::SyntaxKind::CaseArm)
            .expect("case arm");
        assert!(
            arm.descendants()
                .any(|node| node.kind() == crate::SyntaxKind::PatternMlApplicationTail),
            "{source:?}"
        );
        assert!(
            arm.children_with_tokens()
                .any(|element| element.kind() == crate::SyntaxKind::Arrow),
            "{source:?}"
        );
    }

    let source = "case x:\n  opt::just fill if accepted -> fill";
    let green = run(source).0;
    assert_eq!(green.to_string(), source);
    assert!(structural_facts(&green).is_empty());
    let root = crate::SyntaxNode::new_root(green);
    assert!(
        root.descendants()
            .any(|node| node.kind() == crate::SyntaxKind::CaseGuard)
    );
}

#[test]
fn arm_pattern_type_annotations_leave_arrows_and_guards_to_the_arm_owner() {
    for (source, arm_kind, guard_kind) in [
        ("case p:\n    x: int -> 1", SyntaxKind::CaseArm, None),
        (
            "case p:\n    x: int if c -> 1",
            SyntaxKind::CaseArm,
            Some(SyntaxKind::CaseGuard),
        ),
        (
            "case p:\n    x: int where c -> 1",
            SyntaxKind::CaseArm,
            Some(SyntaxKind::CaseGuard),
        ),
        ("catch e:\n    x: int -> 1", SyntaxKind::CatchArm, None),
        (
            "catch e:\n    x: int if c -> 1",
            SyntaxKind::CatchArm,
            Some(SyntaxKind::CatchGuard),
        ),
        (
            "catch e:\n    x: int where c -> 1",
            SyntaxKind::CatchArm,
            Some(SyntaxKind::CatchGuard),
        ),
    ] {
        let root = case_like_literal_production(source);
        let arm = root
            .descendants()
            .find(|node| node.kind() == arm_kind)
            .expect("annotated arm");
        let annotation = arm
            .descendants()
            .find(|node| node.kind() == SyntaxKind::PatternTypeAnnotation)
            .expect("arm PatternTypeAnnotation");
        assert!(
            annotation
                .descendants_with_tokens()
                .filter_map(|element| element.into_token())
                .any(|token| token.kind() == SyntaxKind::Identifier && token.text() == "int"),
            "{source:?}"
        );
        assert!(
            !annotation
                .descendants()
                .any(|node| node.kind() == SyntaxKind::TypeArrowTail),
            "{source:?}"
        );
        assert_eq!(
            arm.children_with_tokens()
                .filter(|element| element.kind() == SyntaxKind::Arrow)
                .count(),
            1,
            "{source:?}"
        );
        assert_eq!(
            arm.children()
                .filter(|node| matches!(
                    node.kind(),
                    SyntaxKind::CaseGuard | SyntaxKind::CatchGuard
                ))
                .map(|node| node.kind())
                .collect::<Vec<_>>(),
            guard_kind.into_iter().collect::<Vec<_>>(),
            "{source:?}"
        );
    }
}

#[test]
fn parenthesized_arm_pattern_annotation_keeps_its_function_type_arrow() {
    for (source, arm_kind) in [
        ("case p:\n    (x: int -> int) -> body", SyntaxKind::CaseArm),
        (
            "catch e:\n    (x: int -> int) -> body",
            SyntaxKind::CatchArm,
        ),
    ] {
        let root = case_like_literal_production(source);
        let arm = root
            .descendants()
            .find(|node| node.kind() == arm_kind)
            .expect("parenthesized annotated arm");
        let annotation = arm
            .descendants()
            .find(|node| node.kind() == SyntaxKind::PatternTypeAnnotation)
            .expect("parenthesized PatternTypeAnnotation");
        assert_eq!(
            annotation
                .descendants()
                .filter(|node| node.kind() == SyntaxKind::TypeArrowTail)
                .count(),
            1,
            "{source:?}"
        );
        assert_eq!(
            arm.children_with_tokens()
                .filter(|element| element.kind() == SyntaxKind::Arrow)
                .count(),
            1,
            "{source:?}"
        );
    }
}

#[test]
fn catch_effect_arm_payload_annotation_keeps_handler_and_arrow_structure() {
    let source = "catch e:\n    op(x: int), k -> k x";
    let root = case_like_literal_production(source);
    let arm = root
        .descendants()
        .find(|node| node.kind() == SyntaxKind::CatchArm)
        .expect("catch effect arm");
    assert_eq!(
        arm.children()
            .filter(|node| node.kind() == SyntaxKind::Pattern)
            .count(),
        2
    );
    assert_eq!(
        arm.descendants()
            .filter(|node| node.kind() == SyntaxKind::PatternTypeAnnotation)
            .count(),
        1
    );
    assert!(
        arm.descendants()
            .any(|node| node.kind() == SyntaxKind::PatternCallTail)
    );
    assert_eq!(
        arm.children_with_tokens()
            .filter(|element| element.kind() == SyntaxKind::Arrow)
            .count(),
        1
    );
}

#[test]
fn arm_pattern_annotation_recovery_preserves_arrow_ownership() {
    let source = "case p:\n    x: int ->";
    let green = run(source).0;
    assert_eq!(green.to_string(), source);
    assert_eq!(
        structural_facts(&green),
        [(StructuralKind::Missing, source.len()..source.len())]
    );
    let root = SyntaxNode::new_root(green);
    let arm = root
        .descendants()
        .find(|node| node.kind() == SyntaxKind::CaseArm)
        .expect("annotated case arm");
    let annotation = arm
        .descendants()
        .find(|node| node.kind() == SyntaxKind::PatternTypeAnnotation)
        .expect("arm PatternTypeAnnotation");
    assert!(!annotation.descendants().any(|node| matches!(
        node.kind(),
        SyntaxKind::Missing | SyntaxKind::Error | SyntaxKind::Invalid
    )));
    assert_eq!(
        arm.children_with_tokens()
            .filter(|element| element.kind() == SyntaxKind::Arrow)
            .count(),
        1
    );
    assert_eq!(
        arm.children()
            .filter(|node| node.kind() == SyntaxKind::Missing)
            .count(),
        1
    );

    let source = "case p:\n    x:";
    let green = run(source).0;
    assert_eq!(green.to_string(), source);
    assert_eq!(
        structural_facts(&green),
        [
            (StructuralKind::Missing, source.len()..source.len()),
            (StructuralKind::Missing, source.len()..source.len()),
        ]
    );
    let root = SyntaxNode::new_root(green);
    let annotation = root
        .descendants()
        .find(|node| node.kind() == SyntaxKind::PatternTypeAnnotation)
        .expect("incomplete PatternTypeAnnotation");
    assert_eq!(
        annotation
            .descendants()
            .filter(|node| node.kind() == SyntaxKind::Missing)
            .count(),
        1
    );
    let arm = root
        .descendants()
        .find(|node| node.kind() == SyntaxKind::CaseArm)
        .expect("incomplete case arm");
    assert_eq!(
        arm.children()
            .filter(|node| node.kind() == SyntaxKind::Missing)
            .count(),
        1
    );
}

#[test]
fn unchanged_yulang2_button_has_complete_symbol_and_pattern_syntax() {
    let source = include_str!("../../../../web/playground/examples/yulang2-button.yu");
    let root = case_like_literal_production(source);
    assert_eq!(
        root.descendants()
            .filter(|node| node.kind() == SyntaxKind::SymbolExpression)
            .count(),
        2
    );
    assert_eq!(
        root.descendants()
            .filter(|node| node.kind() == SyntaxKind::SymbolPattern)
            .count(),
        2
    );
    assert_eq!(
        root.descendants()
            .filter(|node| node.kind() == SyntaxKind::CaseArm)
            .flat_map(|arm| arm.descendants().collect::<Vec<_>>())
            .filter(|node| node.kind() == SyntaxKind::PatternMlApplicationTail)
            .count(),
        1
    );
}

#[test]
fn symbol_expression_statements_keep_declaration_and_nested_owners() {
    for source in [
        ":disabled\n",
        "my x = :ok\n:disabled\n",
        "struct S{x:T}\n:ok\n",
        "my f = { :ok }",
        "my f =\n    :ok\n",
        "mod M {}\n:ok\n",
    ] {
        let root = case_like_literal_production(source);
        assert!(
            root.descendants()
                .any(|node| node.kind() == SyntaxKind::SymbolExpression),
            "{source}"
        );
    }
}

#[test]
fn explicit_constructor_patterns_retain_all_payloads_and_arm_frontiers() {
    for (source, payloads) in [
        ("case x: :label text -> text", 1),
        ("case x: :pair left right -> left", 2),
        ("case x: option::pair left right -> left", 2),
        ("case x: :pair left right if accepted -> left", 2),
        ("case x: :label text where accepted -> text", 1),
        ("case x:\n  :label text -> text\n  :disabled -> 0", 1),
    ] {
        let green = run(source).0;
        assert_eq!(green.to_string(), source);
        assert!(structural_facts(&green).is_empty(), "{source:?}");
        let root = crate::SyntaxNode::new_root(green);
        let arm = root
            .descendants()
            .find(|node| node.kind() == SyntaxKind::CaseArm)
            .unwrap();
        let pattern = arm
            .children()
            .find(|node| node.kind() == SyntaxKind::Pattern)
            .unwrap();
        assert_eq!(
            pattern
                .children()
                .filter(|node| node.kind() == SyntaxKind::PatternMlApplicationTail)
                .count(),
            payloads,
            "{source:?}"
        );
        assert!(
            arm.children_with_tokens()
                .any(|element| element.kind() == SyntaxKind::Arrow),
            "{source:?}"
        );
    }
    // Plain heads keep the caller's existing recovery boundary.
    let green = run("case x: name value -> value").0;
    assert!(!structural_facts(&green).is_empty());
    assert!(
        !crate::SyntaxNode::new_root(green)
            .descendants()
            .any(|node| node.kind() == SyntaxKind::PatternMlApplicationTail)
    );
}

#[test]
fn catch_sequence_matching_close_after_trailing_comma_is_owned_by_block() {
    for source in [
        "catch x { n -> a, }",
        "catch x { n -> a,\r\n }",
        "catch x { n -> a, _ -> b }",
        "catch x { n -> a\n _ -> b }",
        "case x: n -> a, _ -> b",
        "case x:\n  n -> a\n  _ -> b",
        "catch x: n -> a",
    ] {
        let operators = OperatorTable::empty();
        let mut recover = Recover::new_for_test(&operators);
        let mut output = GreenNodeBuilder::new();
        output.start_node(SyntaxKind::Root.into());
        let (_, suffix) = parse_case_into(source, 0, None, &mut recover, &mut output);
        output.finish_node();
        let green = finish_with_discarded_recoveries(output, recover);
        let facts = structural_facts(&green);
        assert_eq!(green.to_string(), source);
        assert_eq!(suffix, "");
        assert!(facts.is_empty(), "{source:?}: {facts:?}");
    }
}

#[test]
fn empty_catch_keeps_required_arm_recovery_before_local_close_completion() {
    for (source, matching_close) in [("catch x {}", true), ("catch x { ]tail", false)] {
        for origin in [0, 8100] {
            let at = 9;
            let mut expected = vec![
                structural_kind_range(
                    0,
                    CstSlot::Pattern,
                    if matching_close {
                        StructuralKind::Missing
                    } else {
                        StructuralKind::ErrorGroup
                    },
                    if matching_close { at..at } else { at..at + 2 },
                ),
                arm_fact(
                    1,
                    CstSlot::Arrow,
                    if matching_close { at..at } else { 15..15 },
                    true,
                    &[],
                ),
            ];
            if !matching_close {
                // With no caller stop, `]` retains the Pattern owner's recovery.
                expected.push(sequence_fact(2, false, 15));
            }
            for _ in 0..1 {
                let operators = OperatorTable::empty();
                let mut recover = Recover::new_for_test(&operators);
                let mut output = GreenNodeBuilder::new();
                output.start_node(SyntaxKind::Root.into());
                let (_, suffix) = parse_case_into(source, origin, None, &mut recover, &mut output);
                output.finish_node();
                let green = finish_with_discarded_recoveries(output, recover);
                let records = structural_facts(&green);
                assert_eq!(records, expected, "{source:?}");
                let root = SyntaxNode::new_root(green);
                assert_eq!(root.to_string(), source);
                assert_eq!(suffix, "");
                let block = root
                    .descendants()
                    .find(|node| node.kind() == SyntaxKind::CatchBlock)
                    .unwrap();
                let arm = block
                    .children()
                    .find(|node| node.kind() == SyntaxKind::CatchArm)
                    .expect("the first arm is mandatory even at a close");
                assert_eq!(
                    arm.descendants()
                        .filter(|node| node.kind() == SyntaxKind::Missing)
                        .count(),
                    if matching_close { 2 } else { 1 }
                );
                assert_eq!(
                    block
                        .descendants()
                        .filter(|node| node.kind() == SyntaxKind::Missing)
                        .count(),
                    2
                );
                if matching_close {
                    assert_eq!(suffix, "");
                    assert_eq!(block.last_token().unwrap().text(), "}");
                } else {
                    assert_eq!(
                        crate::tests::recovery_output::recovery_groups(&arm)
                            .into_iter()
                            .next()
                            .unwrap()
                            .to_string(),
                        " ]"
                    );
                    assert_eq!(block.last_child().unwrap().kind(), SyntaxKind::Missing);
                }
            }
        }
    }
}

#[test]
fn case_e12i_literal_retains_current_ml_and_operator_judgment() {
    let source = "case x: 1 -> a 2 -> b";
    let operators = OperatorTable::empty();
    let mut recover = Recover::new_for_test(&operators);
    let mut output = GreenNodeBuilder::new();
    output.start_node(SyntaxKind::Root.into());
    let (_, suffix) = parse_case_into(source, 0, None, &mut recover, &mut output);
    output.finish_node();
    let green = finish_with_discarded_recoveries(output, recover);
    let records = structural_facts(&green);
    assert_eq!(suffix, "> b");
    assert!(records.is_empty());
}

#[test]
fn catch_local_close_keeps_protected_item_and_follows_child_facts() {
    use crate::lexical::yumark::{FenceOpener, FencePrefixPolicy};
    let fence = FenceBoundary {
        opener: FenceOpener {
            line: 0,
            marker: 0..3,
            marker_width: 3,
        },
        prefix_policy: FencePrefixPolicy::ActivePrefixQuote { depth: 2, base: 0 },
        close_column: 0,
    };
    for head in [
        "catch α { n -> a",
        "catch α { n -> a,",
        "catch α { n",
        "catch α { n -> @",
    ] {
        for suffix in [" ]tail", "\r\n> > ```\r\nouter", "\r\n> foreign"] {
            let source = format!("{head}{suffix}");
            let origin = 7200;
            let fenced = suffix.contains('>');
            let at = head.len();
            let mut expected = Vec::new();
            if head.ends_with(" n") {
                expected.push(arm_fact(0, CstSlot::Arrow, at..at, true, &[]));
            } else if head.ends_with('@') {
                let start = head.len() - 1;
                expected.push(arm_fact(
                    0,
                    CstSlot::Body,
                    start..start + 1,
                    false,
                    &[start..start + 1],
                ));
            }
            expected.push(sequence_fact(expected.len() as u32, false, at));
            for _ in 0..1 {
                let operators = OperatorTable::empty();
                let mut recover = Recover::new_for_test(&operators);
                let mut output = GreenNodeBuilder::new();
                output.start_node(SyntaxKind::Root.into());
                let (exit, remainder) = parse_case_into(
                    &source,
                    origin,
                    fenced.then_some(&fence),
                    &mut recover,
                    &mut output,
                );
                output.finish_node();
                let green = finish_with_discarded_recoveries(output, recover);
                let records = structural_facts(&green);
                assert_eq!(records, expected, "{source:?}");
                assert_eq!(green.to_string(), head, "{source:?}");
                let NormalizedExit::Complete(Err(Either::Left(mut item)), line) = exit else {
                    panic!("pending {source:?}")
                };
                let successor = origin + source.len() - remainder.len();
                assert_eq!(
                    item.extent(successor).recovery_range().start,
                    origin + head.len()
                );
                if fenced {
                    assert!(item.payload_view().is_boundary());
                    assert_eq!(remainder, suffix.strip_prefix("\r\n").unwrap());
                    assert_eq!(line, LineEntry::PhysicalStart);
                } else {
                    assert_eq!(token_kind(&item), Some(TokenKind::RBracket));
                    assert_eq!(emit_pending_leading_text(&mut item), " ");
                    assert_eq!(remainder, "tail");
                    assert_eq!(line, LineEntry::InLine);
                }
            }
        }
    }
}

fn arm_fact(
    _: u32,
    _: CstSlot,
    range: Range<usize>,
    _: bool,
    tokens: &[Range<usize>],
) -> StructuralFact {
    (
        if tokens.is_empty() {
            StructuralKind::Missing
        } else {
            StructuralKind::ErrorGroup
        },
        range,
    )
}

fn structural_kind_range(
    _: u32,
    _: CstSlot,
    kind: StructuralKind,
    range: Range<usize>,
) -> StructuralFact {
    (
        if kind == StructuralKind::Missing {
            StructuralKind::Missing
        } else {
            StructuralKind::ErrorGroup
        },
        range,
    )
}

fn parse_case_into<'s>(
    source: &'s str,
    origin: usize,
    fence: Option<&FenceBoundary>,
    recover: &mut Recover,
    output: &mut GreenNodeBuilder,
) -> (NormalizedExit, &'s str) {
    let mut input = source;
    let exit = expr_normalized(
        crate::cursor::SyntaxIn::new(&mut input, recover, output),
        None,
        0,
        0,
        MlMode::All,
        StatementLineHandoff::OrdinaryLayout,
        origin,
        LineEntry::InLine,
        fence,
        Some(AmbientClaimView::root_statement(0)).into(),
        None,
    )
    .expect("CaseLike expression");
    (exit, input)
}

#[test]
fn case_structural_slots_have_exact_cst_kind_and_range_facts() {
    use CstSlot::{Arm, Block, Handler, Pattern};
    use StructuralKind::{ErrorGroup as Error, Missing};
    for (source, role, kind, range) in [
        ("case x", Block, StructuralKind::Missing, 6..6),
        ("catch action", Block, Missing, 12..12),
        ("case x  ", Block, Missing, 8..8),
        ("catch action  ", Block, Missing, 14..14),
        ("case x: -> a", Pattern, Missing, 8..8),
        ("case x:", Pattern, Missing, 7..7),
        ("catch x: err,", Handler, Missing, 13..13),
        ("catch action: err, -> recover", Handler, Missing, 18..18),
        ("case x:\nnext", Arm, Missing, 7..7),
        ("catch x:\nnext", Arm, Missing, 8..8),
        ("case x: @ n -> a", Pattern, Error, 8..9),
        ("case x: @", Pattern, Error, 8..9),
        ("catch x: @ err -> a", Pattern, Error, 9..10),
        ("catch x: err, @ handler -> a", Handler, Error, 13..15),
        ("case α: @ 💥 n -> a", Pattern, Error, 9..15),
        ("(case x)", Block, Missing, 7..7),
        ("(case x: -> a)", Pattern, Missing, 9..9),
        ("(catch action: err, -> recover)", Handler, Missing, 19..19),
    ] {
        for origin in [0, 8100] {
            let mut expected = vec![structural_kind_range(0, role, kind, range.clone())];
            match source {
                "case x:" | "catch x: err," => {
                    expected.push((StructuralKind::Missing, range.end..range.end));
                }
                "case x: @" => expected.push((StructuralKind::Missing, 9..9)),
                _ => {}
            }
            let mut fresh = None;
            for _ in 0..1 {
                let operators = OperatorTable::empty();
                let mut recover = Recover::new_for_test(&operators);
                let mut output = GreenNodeBuilder::new();
                output.start_node(SyntaxKind::Root.into());
                let (mut exit, remainder) =
                    parse_case_into(source, origin, None, &mut recover, &mut output);
                if let NormalizedExit::Complete(Err(Either::Right(end)), _) = &mut exit {
                    emit_end(&mut output, end);
                }
                output.finish_node();
                let green = finish_with_discarded_recoveries(output, recover);
                let records = structural_facts(&green);
                assert_eq!(records, expected, "{source:?}");
                assert_eq!(
                    green.to_string(),
                    if role == Arm {
                        source.split('\n').next().unwrap()
                    } else {
                        source
                    },
                    "{source:?}"
                );
                assert_eq!(remainder, "");
                if let Some(fresh) = &fresh {
                    assert_eq!(&green, fresh);
                } else {
                    fresh = Some(green);
                }
            }
        }
    }
}

fn expression(root: &SyntaxNode, kind: SyntaxKind) -> SyntaxNode {
    root.descendants()
        .find(|node| node.kind() == kind)
        .expect("case-like expression")
}

// Gate-1 evidence intentionally reads only Rowan occurrences.
fn case_schema_children(node: &SyntaxNode) -> Vec<SyntaxKind> {
    node.children_with_tokens()
        .filter(|child| !matches!(child.kind(), SyntaxKind::Whitespace | SyntaxKind::Newline))
        .map(|child| {
            assert_eq!(child.parent(), Some(node.clone()));
            match child.kind() {
                SyntaxKind::Missing => {
                    assert!(child.as_node().is_some());
                    assert!(child.text_range().is_empty());
                }
                SyntaxKind::Error => {
                    assert!(child.as_token().is_some());
                    assert!(!child.text_range().is_empty());
                }
                _ => {}
            }
            child.kind()
        })
        .collect()
}

#[test]
fn case_schema_expression_and_pattern_slots_use_ordered_rowan_children() {
    use SyntaxKind::*;
    for (head, scrutinee, guard, arm) in [
        ("case", CaseScrutinee, CaseGuard, CaseArm),
        ("catch", CatchScrutinee, CatchGuard, CatchArm),
    ] {
        for (payload, expected) in [
            ("", vec![Missing]),
            ("@", vec![Error]),
            ("@ x", vec![Error, IdentifierExpression]),
        ] {
            for (source, owner) in [
                (format!("{head} {payload}: n -> yes"), scrutinee),
                (format!("{head} x: n if {payload} -> yes"), guard),
            ] {
                let root = SyntaxNode::new_root(run(&source).0);
                assert_eq!(root.to_string(), source);
                let slot = expression(&root, owner);
                let mut children = case_schema_children(&slot);
                if owner == guard {
                    assert_eq!(children.remove(0), IfKw);
                }
                assert_eq!(children, [OperatorChain], "{source}");
                let chain = slot.children().find(|n| n.kind() == OperatorChain).unwrap();
                assert_eq!(case_schema_children(&chain), expected, "{source}");
                for child in chain
                    .children_with_tokens()
                    .filter(|c| matches!(c.kind(), Missing | Error))
                {
                    assert_eq!(child.parent(), Some(chain.clone()));
                    assert_eq!(child.text_range().is_empty(), child.kind() == Missing);
                }
            }
        }
        for payload in ["", "@", "@ n"] {
            let source = format!("{head} x: {payload} -> yes");
            let root = SyntaxNode::new_root(run(&source).0);
            let owner = expression(&root, arm);
            let pattern = owner.children().find(|n| n.kind() == Pattern).unwrap();
            let children = case_schema_children(&pattern);
            assert_eq!(
                children[0],
                if payload.is_empty() { Missing } else { Error },
                "{source}"
            );
            assert_eq!(
                children.len(),
                if payload == "@ n" { 2 } else { 1 },
                "{source}"
            );
            assert_eq!(pattern.parent(), Some(owner));
        }
    }
    for payload in ["", "@", "@ handler"] {
        let source = format!("catch x: err, {payload} -> yes");
        let root = SyntaxNode::new_root(run(&source).0);
        let arm = expression(&root, CatchArm);
        let children = case_schema_children(&arm);
        assert_eq!(&children[..3], &[Pattern, Comma, Pattern], "{source}");
        let handler = arm
            .children()
            .filter(|n| n.kind() == Pattern)
            .nth(1)
            .unwrap();
        let mut children = case_schema_children(&handler);
        let errors: Vec<_> = handler
            .children_with_tokens()
            .filter(|n| n.kind() == Error)
            .collect();
        for pair in errors.windows(2) {
            assert_eq!(pair[0].text_range().end(), pair[1].text_range().start());
            assert_eq!(pair[0].next_sibling_or_token(), Some(pair[1].clone()));
        }
        children.dedup(); // adjacent Error fragments constitute one initial slot run
        assert_eq!(
            children[0],
            if payload.is_empty() { Missing } else { Error }
        );
        assert_eq!(children.len(), if payload == "@ handler" { 2 } else { 1 });
    }
}

#[test]
fn case_schema_where_guard_missing_error_and_retry_use_ordered_rowan_children() {
    use SyntaxKind::*;
    for (head, expression_kind, block_kind, arm_kind, guard_kind) in [
        ("case", CaseExpression, CaseBlock, CaseArm, CaseGuard),
        ("catch", CatchExpression, CatchBlock, CatchArm, CatchGuard),
    ] {
        for payload in ["", "@ @", "@ @ g"] {
            let source = format!("{head} x: n where {payload} -> yes");
            let h = head.len();
            let root = SyntaxNode::new_root(run(&source).0);
            assert_eq!(root.to_string(), source);
            let range = |element: &rowan::NodeOrToken<SyntaxNode, crate::SyntaxToken>| {
                usize::from(element.text_range().start())..usize::from(element.text_range().end())
            };
            let guard = expression(&root, guard_kind);
            let ancestry: Vec<_> = guard.ancestors().map(|node| node.kind()).collect();
            assert_eq!(
                ancestry,
                [
                    guard_kind,
                    arm_kind,
                    block_kind,
                    expression_kind,
                    OperatorChain,
                    Root
                ],
                "{source}"
            );
            for kind in [expression_kind, block_kind, arm_kind, guard_kind] {
                assert_eq!(
                    root.descendants()
                        .filter(|node| node.kind() == kind)
                        .count(),
                    1
                );
            }
            let arm = guard.parent().unwrap();
            let guard_children: Vec<_> = guard.children_with_tokens().collect();
            assert_eq!(
                guard_children
                    .iter()
                    .map(|child| child.kind())
                    .collect::<Vec<_>>(),
                [WhereKw, Whitespace, OperatorChain]
            );
            for child in &guard_children {
                assert_eq!(child.parent(), Some(guard.clone()));
            }
            assert!(guard_children[0].as_token().is_some());
            assert_eq!(guard_children[0].to_string(), "where");
            assert_eq!(range(&guard_children[0]), h + 6..h + 11);
            let empty = payload.is_empty();
            let retry = payload == "@ @ g";
            let chain_start = h + if empty { 13 } else { 12 };
            let chain_end = h + if empty {
                13
            } else if retry {
                17
            } else {
                15
            };
            assert_eq!(range(&guard_children[1]), h + 11..chain_start);
            assert_eq!(
                guard_children[1].to_string(),
                if empty { "  " } else { " " }
            );
            assert!(guard_children[1].as_token().is_some());
            let chain = guard_children[2].as_node().unwrap();
            assert_eq!(range(&guard_children[2]), chain_start..chain_end);
            assert_eq!(range(&guard.clone().into()), h + 6..chain_end);
            let children: Vec<_> = chain.children_with_tokens().collect();
            for child in &children {
                assert_eq!(child.parent(), Some(chain.clone()));
            }
            let expected_children = if empty {
                vec![Missing]
            } else if retry {
                vec![Error, Error, Error, IdentifierExpression]
            } else {
                vec![Error, Error, Error]
            };
            assert_eq!(
                children
                    .iter()
                    .map(|child| child.kind())
                    .collect::<Vec<_>>(),
                expected_children
            );
            let recovery_range = if empty {
                let missing = children[0].as_node().unwrap();
                assert_eq!(missing.children_with_tokens().count(), 0);
                assert_eq!(range(&children[0]), h + 13..h + 13);
                range(&children[0])
            } else {
                for (index, text) in ["@", " ", "@"].into_iter().enumerate() {
                    assert!(children[index].as_token().is_some());
                    assert_eq!(children[index].to_string(), text);
                    assert_eq!(range(&children[index]), h + 12 + index..h + 13 + index);
                }
                for pair in children[..3].windows(2) {
                    assert_eq!(pair[0].next_sibling_or_token(), Some(pair[1].clone()));
                    assert_eq!(pair[0].text_range().end(), pair[1].text_range().start());
                }
                assert!(children[0].prev_sibling_or_token().is_none());
                assert_eq!(
                    children[2]
                        .next_sibling_or_token()
                        .map(|child| child.kind()),
                    retry.then_some(IdentifierExpression)
                );
                range(&children[0]).start..range(&children[2]).end
            };
            let recovery: Vec<_> = root
                .descendants_with_tokens()
                .filter(|child| matches!(child.kind(), Missing | Error | Invalid))
                .collect();
            assert_eq!(recovery, children[..if empty { 1 } else { 3 }]);
            if retry {
                let admitted = children[3].as_node().unwrap();
                assert_eq!(range(&children[3]), h + 15..h + 17);
                let tokens: Vec<_> = admitted.children_with_tokens().collect();
                assert_eq!(tokens.len(), 2);
                for (token, kind, text, span) in [
                    (&tokens[0], Whitespace, " ", h + 15..h + 16),
                    (&tokens[1], Identifier, "g", h + 16..h + 17),
                ] {
                    assert_eq!(token.parent(), Some(admitted.clone()));
                    assert!(token.as_token().is_some());
                    assert_eq!(token.kind(), kind);
                    assert_eq!(token.to_string(), text);
                    assert_eq!(range(token), span);
                }
            }
            let arm_children: Vec<_> = arm.children_with_tokens().collect();
            let guard_index = arm_children
                .iter()
                .position(|child| child == &guard.clone().into())
                .unwrap();
            let leading = &arm_children[guard_index - 1];
            assert_eq!(leading.kind(), Whitespace);
            assert!(leading.as_token().is_some());
            assert_eq!(leading.to_string(), " ");
            assert_eq!(range(leading), h + 5..h + 6);
            let mut successor = guard_index + 1;
            if !empty {
                let leading = &arm_children[successor];
                assert_eq!(leading.kind(), Whitespace);
                assert!(leading.as_token().is_some());
                assert_eq!(leading.to_string(), " ");
                assert_eq!(range(leading), chain_end..chain_end + 1);
                successor += 1;
            }
            let arrow = &arm_children[successor];
            let arrow_start = chain_end + usize::from(!empty);
            assert_eq!(arrow.kind(), Arrow);
            assert!(arrow.as_token().is_some());
            assert_eq!(arrow.to_string(), "->");
            assert_eq!(range(arrow), arrow_start..arrow_start + 2);
            for child in &arm_children {
                assert_eq!(child.parent(), Some(arm.clone()));
            }
            let body = arm_children.last().unwrap().as_node().unwrap();
            assert_eq!(body.kind(), OperatorChain);
            assert_eq!(body.to_string().trim(), "yes");
            assert!(body.text_range().start() >= arrow.text_range().end());
            assert!(!body.ancestors().any(|node| node == guard));

            // Select the slot from the complete family ancestry and the direct
            // WhereKw -> OperatorChain grammar.
            let projection = match (ancestry.as_slice(), guard_children[0].kind(), chain.kind()) {
                (
                    [
                        CaseGuard,
                        CaseArm,
                        CaseBlock,
                        CaseExpression,
                        OperatorChain,
                        Root,
                    ]
                    | [
                        CatchGuard,
                        CatchArm,
                        CatchBlock,
                        CatchExpression,
                        OperatorChain,
                        Root,
                    ],
                    WhereKw,
                    OperatorChain,
                ) => (
                    CstSlot::Guard,
                    [ExpectedSyntax::Expression],
                    0usize,
                    recovery_range,
                ),
                _ => panic!("not a complete where-guard slot: {source}"),
            };
            assert_eq!(
                projection,
                (
                    CstSlot::Guard,
                    [ExpectedSyntax::Expression],
                    0,
                    if empty {
                        h + 13..h + 13
                    } else {
                        h + 12..h + 15
                    },
                )
            );
        }
    }
}

#[test]
fn case_schema_arm_and_block_slots_keep_distinct_direct_occurrences() {
    use SyntaxKind::*;
    for (head, block_kind, arm_kind) in [
        ("case", CaseBlock, CaseArm),
        ("catch", CatchBlock, CatchArm),
    ] {
        let root = SyntaxNode::new_root(run(&format!("{head} x")).0);
        assert_eq!(
            case_schema_children(&expression(&root, block_kind)),
            [Missing]
        );
        let root = SyntaxNode::new_root(run(&format!("{head} x:\nnext")).0);
        assert_eq!(
            case_schema_children(&expression(&root, arm_kind)),
            [Missing]
        );
        for (tail, expected) in [
            ("yes", vec![Pattern, Missing, OperatorChain]),
            ("->", vec![Pattern, Arrow, Missing]),
            ("", vec![Pattern, Missing]),
            ("@", vec![Pattern, Missing, Error]),
            ("@ yes", vec![Pattern, Missing, Error, OperatorChain]),
            ("-> @", vec![Pattern, Arrow, Error]),
            ("-> @ yes", vec![Pattern, Arrow, Error, OperatorChain]),
        ] {
            let source = format!("{head} x: n {tail}");
            let root = SyntaxNode::new_root(run(&source).0);
            let arm = expression(&root, arm_kind);
            assert_eq!(case_schema_children(&arm), expected, "{source}");
            for missing in arm.children().filter(|n| n.kind() == Missing) {
                assert!(missing.text_range().is_empty());
                assert_eq!(missing.parent(), Some(arm.clone()));
            }
        }
    }
    // WP-7 removed the row for 'n -> [tail] -> yes': with list literals every pattern start is also an expression start, so an unread pattern-only opener no longer exists (design memo WP-7).
    for source in [
        "catch x { n -> yes",
        "catch x { n",
        "catch x { n -> @",
        "catch α { n ->",
    ] {
        let root = SyntaxNode::new_root(run(source).0);
        let block = expression(&root, CatchBlock);
        let children = case_schema_children(&block);
        assert_eq!(children, [LBrace, CatchArm, Missing], "{source}");
        let close = block.last_child().unwrap();
        assert_eq!(usize::from(close.text_range().start()), source.len());
        assert!(close.text_range().is_empty());
        if source.ends_with('n') || source.ends_with("->") {
            let arm = expression(&block, CatchArm);
            assert_eq!(arm.last_child().unwrap().text_range(), close.text_range());
        }
    }
}

#[test]
fn case_schema_indented_statement_owner_and_accepted_controls() {
    use SyntaxKind::*;
    for (head, arm_kind) in [("case", CaseArm), ("catch", CatchArm)] {
        for (payload, expected) in [
            ("", vec![Missing]),
            ("@", vec![Error]),
            ("@ yes", vec![Error, Statement]),
        ] {
            let source = format!("{head} α: n ->\r\n  {payload}");
            let root = SyntaxNode::new_root(run(&source).0);
            assert_eq!(root.to_string(), source);
            let arm = expression(&root, arm_kind);
            assert_eq!(
                case_schema_children(&arm),
                [Pattern, Arrow, IndentedStatementBlock]
            );
            let block = arm
                .children()
                .find(|n| n.kind() == IndentedStatementBlock)
                .unwrap();
            // This direct Arm -> IndentedStatementBlock path selects the shared
            // ColonApplication(IndentedStatement) slot, not the inline Body slot.
            assert_eq!(block.parent(), Some(arm));
            assert_eq!(case_schema_children(&block), expected);
            if let Some(error) = block.children_with_tokens().find(|n| n.kind() == Error) {
                assert_eq!(
                    usize::from(error.text_range().start()),
                    source.find('@').unwrap()
                );
                assert_eq!(error.text_range().len(), 1.into());
            }
        }
    }
    for source in [
        "case x: n -> yes, _ -> no",
        "catch x: n, handler -> yes",
        "catch x { n -> yes, }",
        "case x:\n  n -> yes\n  _ -> no",
        "catch x {\n  n -> yes\n  _ -> no\n}",
    ] {
        let root = SyntaxNode::new_root(run(source).0);
        assert_eq!(root.to_string(), source);
        assert!(
            !root
                .descendants_with_tokens()
                .any(|n| matches!(n.kind(), Missing | Error | Invalid)),
            "{source}"
        );
    }
}

#[test]
fn case_arrow_body_facts_are_exact_at_source_offsets() {
    use CstSlot::{Arrow, Body};
    for (source, specifications) in [
        ("case x: n yes", vec![(Arrow, 10..10, false, vec![])]),
        ("case x: n ->", vec![(Body, 12..12, false, vec![])]),
        ("case x: n", vec![(Arrow, 9..9, true, vec![])]),
        ("case x: n if yes", vec![(Arrow, 16..16, true, vec![])]),
        ("case x: n  ", vec![(Arrow, 11..11, true, vec![])]),
        ("catch x: err, handler", vec![(Arrow, 21..21, true, vec![])]),
        (
            "catch x: err, handler ->",
            vec![(Body, 24..24, false, vec![])],
        ),
        (
            "catch x: err, handler yes",
            vec![(Arrow, 22..22, false, vec![])],
        ),
        (
            "case x: n @, _ -> b",
            vec![
                (Arrow, 10..10, false, vec![]),
                (Body, 10..11, false, vec![10..11]),
            ],
        ),
        (
            "case x: n -> @, _ -> b",
            vec![(Body, 13..14, false, vec![13..14])],
        ),
        (
            "case x: n -> @  ",
            vec![(Body, 13..14, false, vec![13..14])],
        ),
        (
            "case x: n -> @ \"yes\"",
            vec![(Body, 13..14, false, vec![13..14])],
        ),
        ("case x: n -> @;", vec![(Body, 13..14, false, vec![13..14])]),
        ("case x: n;", vec![(Arrow, 9..9, true, vec![])]),
        ("case x: n ->;", vec![(Body, 12..12, false, vec![])]),
        (
            "case α: n -> @ 💥 yes",
            vec![(Body, 14..20, false, vec![14..15, 15..20])],
        ),
    ] {
        let expected_at = |first_id| {
            specifications
                .iter()
                .enumerate()
                .map(|(index, (role, range, combined, tokens))| {
                    let tokens: Vec<_> = tokens.clone();
                    arm_fact(
                        first_id + index as u32,
                        *role,
                        range.clone(),
                        *combined,
                        &tokens,
                    )
                })
                .collect::<Vec<_>>()
        };
        for origin in [0, 9100] {
            let expected = expected_at(0);
            let mut fresh = None;
            for _ in 0..1 {
                let operators = OperatorTable::empty();
                let mut recover = Recover::new_for_test(&operators);
                let mut output = GreenNodeBuilder::new();
                output.start_node(SyntaxKind::Root.into());
                let (mut exit, remainder) =
                    parse_case_into(source, origin, None, &mut recover, &mut output);
                if let NormalizedExit::Complete(Err(Either::Right(end)), _) = &mut exit {
                    emit_end(&mut output, end);
                }
                output.finish_node();
                let green = finish_with_discarded_recoveries(output, recover);
                let records = structural_facts(&green);
                assert_eq!(records, expected, "{source:?}");
                assert_eq!(green.to_string(), source, "{source:?}");
                assert_eq!(remainder, "");
                if let Some(fresh) = &fresh {
                    assert_eq!(&green, fresh);
                } else {
                    fresh = Some(green);
                }
            }
        }
    }
}

#[test]
fn case_arrow_body_combined_absence_keeps_prior_owner_facts_in_order() {
    for (source, role, kind, range, at) in [
        (
            "case x:",
            CstSlot::Pattern,
            StructuralKind::Missing,
            7..7,
            7,
        ),
        (
            "case x: @",
            CstSlot::Pattern,
            StructuralKind::ErrorGroup,
            8..9,
            9,
        ),
        (
            "catch x: err,",
            CstSlot::Handler,
            StructuralKind::Missing,
            13..13,
            13,
        ),
        (
            "case x: n if",
            CstSlot::Guard,
            StructuralKind::Missing,
            12..12,
            12,
        ),
    ] {
        let mut prior = structural_kind_range(0, role, kind, range.clone());
        if role == CstSlot::Guard {
            prior = arm_fact(0, role, range, false, &[]);
        }
        let expected = [prior, arm_fact(1, CstSlot::Arrow, at..at, true, &[])];
        for _ in 0..1 {
            let operators = OperatorTable::empty();
            let mut recover = Recover::new_for_test(&operators);
            let mut output = GreenNodeBuilder::new();
            output.start_node(SyntaxKind::Root.into());
            let _ = parse_case_into(source, 0, None, &mut recover, &mut output);
            output.finish_node();
            let green = finish_with_discarded_recoveries(output, recover);
            let records = structural_facts(&green);
            assert_eq!(records, expected, "{source:?}");
            assert_eq!(
                SyntaxNode::new_root(green)
                    .descendants()
                    .filter(|node| node.kind() == SyntaxKind::Missing)
                    .count(),
                if kind == StructuralKind::Missing {
                    2
                } else {
                    1
                }
            );
        }
    }
}

#[test]
fn case_arrow_body_keeps_protected_boundaries_before_and_after_error() {
    // WP-7: `[` is now a list-literal expression start; the probe token was replaced to keep this contract.
    use crate::lexical::yumark::{FenceOpener, FencePrefixPolicy};
    let fence = FenceBoundary {
        opener: FenceOpener {
            line: 0,
            marker: 0..3,
            marker_width: 3,
        },
        prefix_policy: FencePrefixPolicy::ActivePrefixQuote { depth: 2, base: 0 },
        close_column: 0,
    };
    for head in [
        "case x: n",
        "case x: n ->",
        "case x: n -> @",
        "catch x: err, handler ->",
        "catch x: err, handler -> @",
    ] {
        for suffix in [
            " ]tail",
            " )tail",
            "\r\nnext",
            "\r\n> > ```\r\nouter",
            "\r\n> foreign",
        ] {
            let source = format!("{head}{suffix}");
            let fenced = suffix.contains('>');
            let origin = 7200;
            let error = head.ends_with('@');
            let combined = !head.contains("->");
            let at = head.len();
            let expected = if error {
                let start = head.find('@').unwrap();
                arm_fact(
                    0,
                    CstSlot::Body,
                    start..start + 1,
                    false,
                    &[start..start + 1],
                )
            } else {
                arm_fact(
                    0,
                    if combined {
                        CstSlot::Arrow
                    } else {
                        CstSlot::Body
                    },
                    at..at,
                    combined,
                    &[],
                )
            };
            for _ in 0..1 {
                let operators = OperatorTable::empty();
                let mut recover = Recover::new_for_test(&operators);
                let mut output = GreenNodeBuilder::new();
                output.start_node(SyntaxKind::Root.into());
                let (exit, remainder) = parse_case_into(
                    &source,
                    origin,
                    fenced.then_some(&fence),
                    &mut recover,
                    &mut output,
                );
                output.finish_node();
                let green = finish_with_discarded_recoveries(output, recover);
                let records = structural_facts(&green);
                assert_eq!(records, [expected.clone()], "{source:?}");
                assert_eq!(green.to_string(), head, "{source:?}");
                let NormalizedExit::Complete(Err(Either::Left(mut item)), line) = exit else {
                    panic!("pending boundary {source:?}")
                };
                let successor = origin + source.len() - remainder.len();
                assert_eq!(
                    item.extent(successor).recovery_range().start,
                    origin + head.len(),
                    "{source:?}"
                );
                if fenced {
                    assert!(item.payload_view().is_boundary());
                    assert_eq!(remainder, suffix.strip_prefix("\r\n").unwrap());
                    assert_eq!(line, LineEntry::PhysicalStart);
                } else {
                    assert_eq!(
                        emit_pending_leading_text(&mut item),
                        if suffix.starts_with('\r') {
                            "\r\n"
                        } else {
                            " "
                        }
                    );
                    assert_eq!(
                        remainder,
                        if suffix.starts_with('\r') { "" } else { "tail" }
                    );
                    assert_eq!(line, LineEntry::InLine);
                }
            }
        }
    }
}

#[test]
fn case_body_lexical_retry_keeps_native_tokens_and_prefix_admission() {
    let operators = OperatorTable::from_declarations([
        OperatorDeclaration::new(
            "-",
            OperatorFixities::new().with_prefix(BindingPower::scalar(40)),
        ),
        OperatorDeclaration::new(
            "+",
            OperatorFixities::new().with_infix(BindingPower::scalar(20), BindingPower::scalar(21)),
        ),
    ])
    .unwrap();
    for source in ["case x: n -> + - yes", "case x: n -> + - @"] {
        let green = crate::cursor::parse_root(source, &operators);
        assert_eq!(green.to_string(), source);
        let facts = structural_facts(&green);
        if source.ends_with('@') {
            // The judge also rejects `- @`: it stays in the same lexical Body run.
            assert_eq!(facts, [(StructuralKind::ErrorGroup, 13..18)]);
            assert!(
                !SyntaxNode::new_root(green)
                    .descendants()
                    .any(|node| node.kind() == SyntaxKind::PrefixOperatorUse)
            );
            continue;
        }
        assert_eq!(facts, [(StructuralKind::ErrorGroup, 13..14)]);
        let root = SyntaxNode::new_root(green);
        assert!(
            root.descendants()
                .any(|node| node.kind() == SyntaxKind::PrefixOperatorUse)
        );
        let error = crate::tests::recovery_output::recovery_groups(&root)
            .into_iter()
            .next()
            .unwrap();
        assert_eq!(error.to_string(), "+");
        // The unchanged NUD judge rejects this infix-only spelling; raw recovery is opaque.
        assert_eq!(error.first_token().unwrap().kind(), SyntaxKind::Error);
        assert_eq!(facts.len(), 1);
    }
}

#[test]
fn case_arm_body_list_literal_replaces_the_old_unread_opener_contract() {
    let source = "case x: n -> [tail] -> yes";
    let operators = OperatorTable::empty();
    let green = crate::cursor::parse_root(source, &operators);
    assert_eq!(green.to_string(), source);
    let facts = structural_facts(&green);
    assert_eq!(facts, [(StructuralKind::ErrorGroup, 20..26)]);
    let root = SyntaxNode::new_root(green);
    let arms = root
        .descendants()
        .filter(|node| node.kind() == SyntaxKind::CaseArm)
        .collect::<Vec<_>>();
    assert_eq!(arms.len(), 1);
    let body = arms[0]
        .children()
        .find(|node| node.kind() == SyntaxKind::OperatorChain)
        .expect("case arm body");
    let list = body
        .children()
        .find(|node| node.kind() == SyntaxKind::ListExpression)
        .expect("list-literal arm body");
    assert_eq!(list.to_string(), "[tail]");
    assert_eq!(
        list.text_range(),
        rowan::TextRange::new(13.into(), 19.into())
    );
    let leftover = root
        .descendants_with_tokens()
        .filter_map(|element| element.into_token())
        .filter(|token| token.kind() == SyntaxKind::Error)
        .map(|token| token.text().to_owned())
        .collect::<String>();
    assert_eq!(leftover, "-> yes");
}

#[test]
fn case_structural_nested_owners_and_following_statements_keep_distinct_facts() {
    for (source, expected) in [
        ("case x: n as -> a", vec![(StructuralKind::Missing, 12..12)]),
        (
            "catch x: err, n as -> a",
            vec![(StructuralKind::Missing, 18..18)],
        ),
        ("case x: n | -> a", vec![(StructuralKind::Missing, 12..12)]),
        (
            "catch x: err, n | -> a",
            vec![(StructuralKind::Missing, 18..18)],
        ),
        (
            "(case x: n : T::)",
            vec![
                (StructuralKind::Missing, 16..16),
                (StructuralKind::Missing, 16..16),
            ],
        ),
        (
            "(catch x: err, n : T::)",
            vec![
                (StructuralKind::Missing, 22..22),
                (StructuralKind::Missing, 22..22),
            ],
        ),
    ] {
        let operators = OperatorTable::empty();
        let mut recover = Recover::new_for_test(&operators);
        let mut output = GreenNodeBuilder::new();
        output.start_node(SyntaxKind::Root.into());
        let _ = parse_case_into(source, 0, None, &mut recover, &mut output);
        output.finish_node();
        let green = finish_with_discarded_recoveries(output, recover);
        let records = structural_facts(&green);
        assert_eq!(records, expected, "{source:?}");
    }
    let operators = OperatorTable::empty();
    // E12k retains its literal; the following Statement remains independently owned.
    for source in [
        "my value = case x:\nnext",
        "my value = case x:\nmy next = 1",
        "my value = catch x:\r\nmy next = 1",
    ] {
        let green = crate::cursor::parse_root(source, &operators);
        assert_eq!(green.to_string(), source);
        let at = source.find(['\r', '\n']).unwrap();
        assert_eq!(
            structural_facts(&green),
            [(StructuralKind::Missing, at..at)]
        );
        let root = SyntaxNode::new_root(green);
        let block = root
            .descendants()
            .find(|node| matches!(node.kind(), SyntaxKind::CaseBlock | SyntaxKind::CatchBlock))
            .unwrap();
        assert_eq!(block.to_string(), ":");
        if source.contains("my next") {
            assert_eq!(
                root.descendants()
                    .filter(|node| node.kind() == SyntaxKind::BindingStatement)
                    .count(),
                2
            );
        }
    }
}

#[test]
fn case_structural_accepted_arm_families_remain_recovery_free() {
    for source in [
        "case x:  n -> a, _ -> b",
        "catch x:  err, handler -> a",
        "catch x {  err, handler -> a }",
        "case x:\n  n -> a\n  _ -> b",
        "catch x:\n  err, handler -> a",
    ] {
        let operators = OperatorTable::empty();
        let mut recover = Recover::new_for_test(&operators);
        let mut output = GreenNodeBuilder::new();
        output.start_node(SyntaxKind::Root.into());
        let (mut exit, remainder) = parse_case_into(source, 0, None, &mut recover, &mut output);
        if let NormalizedExit::Complete(Err(Either::Right(end)), _) = &mut exit {
            emit_end(&mut output, end);
        }
        output.finish_node();
        let green = finish_with_discarded_recoveries(output, recover);
        let records = structural_facts(&green);
        assert_eq!(green.to_string(), source);
        assert!(records.is_empty(), "{source:?}: {records:?}");
        assert_eq!(remainder, "");
    }
}

#[test]
fn case_structural_block_and_arm_keep_protected_items_and_foreign_prefix_coordinates() {
    use crate::lexical::yumark::{FenceOpener, FencePrefixPolicy};
    for (source, emitted, at, kind) in [
        ("case x ;", "case x ", 7, TokenKind::Semicolon),
        ("case x  ]", "case x", 6, TokenKind::RBracket),
        ("catch x  }", "catch x", 7, TokenKind::RBrace),
    ] {
        let operators = OperatorTable::empty();
        let mut recover = Recover::new_for_test(&operators);
        let mut output = GreenNodeBuilder::new();
        output.start_node(SyntaxKind::Root.into());
        let (exit, remainder) = parse_case_into(source, 200, None, &mut recover, &mut output);
        output.finish_node();
        let green = finish_with_discarded_recoveries(output, recover);
        let records = structural_facts(&green);
        assert_eq!(green.to_string(), emitted);
        assert_eq!(
            records,
            [structural_kind_range(
                0,
                CstSlot::Block,
                StructuralKind::Missing,
                at..at
            )]
        );
        let NormalizedExit::Complete(Err(Either::Left(item)), _) = exit else {
            panic!("pending block boundary")
        };
        assert_eq!(token_kind(&item), Some(kind));
        assert_eq!(
            item.extent(200 + source.len() - remainder.len())
                .recovery_range()
                .start,
            200 + at
        );
    }
    let fence = FenceBoundary {
        opener: FenceOpener {
            line: 0,
            marker: 0..3,
            marker_width: 3,
        },
        prefix_policy: FencePrefixPolicy::ActivePrefixQuote { depth: 2, base: 0 },
        close_column: 0,
    };
    for (head, role, error) in [
        ("case α: @", CstSlot::Pattern, true),
        ("catch α: err,", CstSlot::Handler, false),
        ("catch α: err, @", CstSlot::Handler, true),
    ] {
        let source = format!("{head}\r\n> > ```\r\nouter");
        let range = if error {
            head.find(',')
                .map_or_else(|| head.find('@').unwrap(), |comma| comma + 1)..head.len()
        } else {
            head.len()..head.len()
        };
        let expected = vec![
            structural_kind_range(
                0,
                role,
                if error {
                    StructuralKind::ErrorGroup
                } else {
                    StructuralKind::Missing
                },
                range,
            ),
            (StructuralKind::Missing, head.len()..head.len()),
        ];
        for _ in 0..1 {
            let operators = OperatorTable::empty();
            let mut recover = Recover::new_for_test(&operators);
            let mut output = GreenNodeBuilder::new();
            output.start_node(SyntaxKind::Root.into());
            let (exit, remainder) =
                parse_case_into(&source, 7000, Some(&fence), &mut recover, &mut output);
            output.finish_node();
            let green = finish_with_discarded_recoveries(output, recover);
            let records = structural_facts(&green);
            assert_eq!(records, expected, "{source:?}");
            assert_eq!(green.to_string(), head);
            let NormalizedExit::Complete(Err(Either::Left(item)), _) = exit else {
                panic!("fence remains pending")
            };
            assert!(item.payload_view().is_boundary());
            assert_eq!(
                item.extent(7000 + source.len() - remainder.len())
                    .recovery_range()
                    .start,
                7000 + head.len()
            );
            assert_eq!(remainder, "> > ```\r\nouter");
        }
    }
    for head in ["case α", "catch α", "case α:", "catch α:"] {
        for suffix in [
            "\r\nnext tail",
            "\nnext tail",
            "\r\n> > ```\r\nouter",
            "\r\n> foreign tail",
        ] {
            let fenced = suffix.contains('>');
            let source = format!("{head}{suffix}");
            let role = if head.ends_with(':') && !fenced {
                CstSlot::Arm
            } else if head.ends_with(':') {
                CstSlot::Pattern
            } else {
                CstSlot::Block
            };
            let origin = 7000;
            let at = head.len();
            let mut expected = vec![structural_kind_range(
                0,
                role,
                StructuralKind::Missing,
                at..at,
            )];
            if head.ends_with(':') && fenced {
                expected.push((StructuralKind::Missing, at..at));
            }
            for _ in 0..1 {
                let operators = OperatorTable::empty();
                let mut recover = Recover::new_for_test(&operators);
                let mut output = GreenNodeBuilder::new();
                output.start_node(SyntaxKind::Root.into());
                let (exit, remainder) = parse_case_into(
                    &source,
                    origin,
                    fenced.then_some(&fence),
                    &mut recover,
                    &mut output,
                );
                output.finish_node();
                let green = finish_with_discarded_recoveries(output, recover);
                let records = structural_facts(&green);
                assert_eq!(records, expected, "{source:?}");
                assert_eq!(green.to_string(), head, "{source:?}");
                let NormalizedExit::Complete(Err(Either::Left(mut item)), _) = exit else {
                    panic!("protected Item {source:?}")
                };
                let successor = origin + source.len() - remainder.len();
                assert_eq!(
                    item.extent(successor).recovery_range().start,
                    origin + head.len()
                );
                if fenced {
                    assert!(item.payload_view().is_boundary());
                } else {
                    assert_eq!(item.payload_view().spelling(), Some("next"));
                    assert_eq!(
                        emit_pending_leading_text(&mut item),
                        if suffix.starts_with("\r") {
                            "\r\n"
                        } else {
                            "\n"
                        }
                    );
                    assert_eq!(remainder, " tail");
                }
            }
        }
    }
    for source in ["(case α  )", "(catch α  )"] {
        let operators = OperatorTable::empty();
        let mut recover = Recover::new_for_test(&operators);
        let mut output = GreenNodeBuilder::new();
        output.start_node(SyntaxKind::Root.into());
        let (mut exit, remainder) = parse_case_into(source, 0, None, &mut recover, &mut output);
        if let NormalizedExit::Complete(Err(Either::Right(end)), _) = &mut exit {
            emit_end(&mut output, end);
        } else {
            panic!("outer close consumed");
        }
        output.finish_node();
        let green = finish_with_discarded_recoveries(output, recover);
        let records = structural_facts(&green);
        let at = source.find("  )").unwrap();
        assert_eq!(
            records,
            [structural_kind_range(
                0,
                CstSlot::Block,
                StructuralKind::Missing,
                at..at
            )]
        );
        assert_eq!(green.to_string(), source);
        assert_eq!(remainder, "");
        let root = SyntaxNode::new_root(green);
        let block = root
            .descendants()
            .find(|node| matches!(node.kind(), SyntaxKind::CaseBlock | SyntaxKind::CatchBlock))
            .unwrap();
        assert_eq!(block.to_string(), "");
        assert!(
            root.descendants_with_tokens()
                .filter_map(|e| e.into_token())
                .any(|t| t.kind() == SyntaxKind::RParen)
        );
    }
}

fn assert_handoff_identifier(exit: &Option<TailExit>, spelling: &str) {
    let Some(Err(Either::Left(item))) = exit else {
        panic!("expected an unconsumed identifier handoff");
    };
    assert_eq!(
        item.payload_view().token_kind(),
        Some(TokenKind::Identifier)
    );
    assert_eq!(item.payload_view().spelling(), Some(spelling));
    assert!(item.leading_view().has_ordinary_newline());
}

#[test]
fn case_like_c7_builds_the_family_specific_inline_topology() {
    let source = "case 'go value: 1 if ready -> yes, _ where fallback -> no,";
    let (green, exit) = run(source);
    assert_eq!(green.to_string(), source);
    assert!(matches!(exit, Some(Err(Either::Right(_)))));

    let root = SyntaxNode::new_root(green);
    let case = expression(&root, SyntaxKind::CaseExpression);
    assert_eq!(
        case.children().map(|node| node.kind()).collect::<Vec<_>>(),
        [
            SyntaxKind::CaseLabel,
            SyntaxKind::CaseScrutinee,
            SyntaxKind::CaseBlock,
        ]
    );
    assert_eq!(
        case.descendants()
            .filter(|node| node.kind() == SyntaxKind::CaseArm)
            .count(),
        2
    );
    assert_eq!(
        case.descendants()
            .filter(|node| node.kind() == SyntaxKind::CaseGuard)
            .count(),
        2
    );
    assert_eq!(
        case.descendants()
            .filter(|node| node.kind() == SyntaxKind::CaseArmSeparator)
            .count(),
        2
    );
    assert_eq!(
        case.descendants_with_tokens()
            .filter_map(|element| element.into_token())
            .filter(|token| token.kind() == SyntaxKind::Arrow)
            .count(),
        2
    );
    assert!(
        !case
            .descendants()
            .any(|node| node.kind() == SyntaxKind::ColonApplicationTail)
    );
}

#[test]
fn case_like_c7_keeps_catch_handler_and_braces_with_catch() {
    let source = "catch action { err, handler -> recover, _ -> fallback }";
    let (green, exit) = run(source);
    assert_eq!(green.to_string(), source);
    assert!(matches!(exit, Some(Err(Either::Right(_)))));

    let root = SyntaxNode::new_root(green);
    let catch = expression(&root, SyntaxKind::CatchExpression);
    let block = catch
        .children()
        .find(|node| node.kind() == SyntaxKind::CatchBlock)
        .expect("CatchBlock");
    assert_eq!(
        block
            .children_with_tokens()
            .filter_map(|element| element.into_token())
            .filter(|token| matches!(token.kind(), SyntaxKind::LBrace | SyntaxKind::RBrace))
            .count(),
        2
    );
    assert_eq!(
        block
            .children()
            .filter(|node| node.kind() == SyntaxKind::CatchArm)
            .count(),
        2
    );
    assert_eq!(
        block
            .descendants()
            .filter(|node| node.kind() == SyntaxKind::CatchArmSeparator)
            .count(),
        1
    );
    let first = block
        .children()
        .find(|node| node.kind() == SyntaxKind::CatchArm)
        .expect("first CatchArm");
    assert_eq!(
        first
            .children()
            .filter(|node| node.kind() == SyntaxKind::Pattern)
            .count(),
        2
    );
    assert!(
        !catch
            .descendants()
            .any(|node| node.kind() == SyntaxKind::BracedStatementBlockExpression)
    );
}

#[test]
fn case_like_c7_keeps_catch_colon_inline_single_and_recovers_required_slots() {
    let source = "catch action: err, handler -> recover";
    let (green, exit) = run(source);
    assert_eq!(green.to_string(), source);
    assert!(matches!(exit, Some(Err(Either::Right(_)))));
    let root = SyntaxNode::new_root(green);
    let catch = expression(&root, SyntaxKind::CatchExpression);
    assert_eq!(
        catch
            .descendants()
            .filter(|node| node.kind() == SyntaxKind::CatchArm)
            .count(),
        1
    );

    let source = "catch action { err -> recover";
    let (green, exit) = run(source);
    assert_eq!(green.to_string(), source);
    assert!(matches!(exit, Some(Err(Either::Right(_)))));
    let root = SyntaxNode::new_root(green);
    let block = root
        .descendants()
        .find(|node| node.kind() == SyntaxKind::CatchBlock)
        .expect("CatchBlock");
    assert_eq!(
        block
            .children()
            .filter(|node| node.kind() == SyntaxKind::Missing)
            .count(),
        1
    );
}

#[test]
fn case_like_c7_keeps_current_depth_brace_newlines_out_of_arm_bodies() {
    let source = "catch action { err -> recover\n  _ -> fallback }";
    let (green, exit) = run(source);
    assert_eq!(green.to_string(), source);
    assert!(matches!(exit, Some(Err(Either::Right(_)))));
    let root = SyntaxNode::new_root(green);
    let catch = expression(&root, SyntaxKind::CatchExpression);
    assert_eq!(
        catch
            .descendants()
            .filter(|node| node.kind() == SyntaxKind::CatchArm)
            .count(),
        2
    );
    assert!(
        !catch
            .descendants()
            .any(|node| node.kind() == SyntaxKind::MlArgument)
    );
}

#[test]
fn case_like_c7_reuses_introduced_body_layout_at_the_arrow_line() {
    let source = "case value:\n  1 ->\n    yes\n  _ -> no";
    let (green, exit) = run(source);
    assert_eq!(green.to_string(), source);
    assert!(matches!(exit, Some(Err(Either::Right(_)))));
    let root = SyntaxNode::new_root(green);
    let case = expression(&root, SyntaxKind::CaseExpression);
    assert_eq!(
        case.descendants()
            .filter(|node| node.kind() == SyntaxKind::CaseArm)
            .count(),
        2
    );
    assert_eq!(
        case.descendants()
            .filter(|node| node.kind() == SyntaxKind::IndentedStatementBlock)
            .count(),
        1
    );

    let source = "case value:\n  1 ->\n  _ -> no";
    let (green, exit) = run(source);
    assert_eq!(green.to_string(), source);
    assert!(matches!(exit, Some(Err(Either::Right(_)))));
    let root = SyntaxNode::new_root(green);
    let case = expression(&root, SyntaxKind::CaseExpression);
    assert_eq!(
        case.descendants()
            .filter(|node| node.kind() == SyntaxKind::CaseArm)
            .count(),
        2
    );
    assert_eq!(
        case.descendants()
            .filter(|node| node.kind() == SyntaxKind::IndentedStatementBlock)
            .count(),
        0
    );
}

#[test]
fn case_like_c7_keeps_pattern_and_guard_boundaries_exact() {
    for source in [
        "case x: :tag -> yes",
        "case x: (a, b) -> yes",
        "case x: n as if -> yes",
        "case x: n if cond -> yes",
        "case x: n where cond -> yes",
    ] {
        let (green, exit) = run(source);
        assert_eq!(green.to_string(), source, "{source:?}");
        assert!(matches!(exit, Some(Err(Either::Right(_)))), "{source:?}");
        let root = SyntaxNode::new_root(green);
        let case = expression(&root, SyntaxKind::CaseExpression);
        assert!(
            case.descendants()
                .any(|node| node.kind() == SyntaxKind::CaseArm),
            "{source:?}"
        );
    }

    let source = "case x: n ->> body";
    let (green, _) = run(source);
    let root = SyntaxNode::new_root(green);
    assert_eq!(
        root.descendants_with_tokens()
            .filter_map(|element| element.into_token())
            .filter(|token| token.kind() == SyntaxKind::Arrow)
            .count(),
        0
    );
    assert_eq!(
        root.descendants_with_tokens()
            .filter_map(|element| element.into_token())
            .filter(|token| token.kind() == SyntaxKind::Error)
            .map(|token| token.text().to_owned())
            .collect::<Vec<_>>(),
        ["->>"],
    );
}

#[test]
fn case_like_c7_returns_outer_delimiters_from_missing_arm_slots() {
    let source = "(case x: ->)";
    let (green, exit) = run(source);
    assert_eq!(green.to_string(), source);
    assert!(matches!(exit, Some(Err(Either::Right(_)))));
    let root = SyntaxNode::new_root(green);
    let case = expression(&root, SyntaxKind::CaseExpression);
    assert_eq!(
        case.descendants()
            .filter(|node| node.kind() == SyntaxKind::Missing)
            .count(),
        2
    );
    assert!(
        root.descendants_with_tokens()
            .filter_map(|element| element.into_token())
            .any(|token| token.kind() == SyntaxKind::RParen)
    );
}

#[test]
fn case_like_c7_prioritizes_exact_nud_keywords_and_preserves_case_brace_nonownership() {
    let operators = OperatorTable::from_declarations([
        OperatorDeclaration::new(
            "case",
            OperatorFixities::new().with_prefix(BindingPower::scalar(40)),
        ),
        OperatorDeclaration::new(
            "catch",
            OperatorFixities::new().with_prefix(BindingPower::scalar(40)),
        ),
    ])
    .expect("contextual case-like table");
    for source in ["case x: n -> yes", "catch x: n -> yes"] {
        let (green, _) = run_with(source, &operators);
        let root = SyntaxNode::new_root(green);
        assert!(
            root.descendants().any(|node| {
                matches!(
                    node.kind(),
                    SyntaxKind::CaseExpression | SyntaxKind::CatchExpression
                )
            }),
            "{source:?}"
        );
    }
    for source in ["casefold", "case?", "catcher", "catch!"] {
        let (green, _) = run_with(source, &operators);
        assert!(
            !SyntaxNode::new_root(green).descendants().any(|node| {
                matches!(
                    node.kind(),
                    SyntaxKind::CaseExpression | SyntaxKind::CatchExpression
                )
            }),
            "{source:?}"
        );
    }

    let (green, _) = run("case x { n -> yes }");
    let root = SyntaxNode::new_root(green);
    let block = root
        .descendants()
        .find(|node| node.kind() == SyntaxKind::CaseBlock)
        .expect("missing case block slot");
    assert!(
        !block
            .descendants_with_tokens()
            .filter_map(|element| element.into_token())
            .any(|token| token.kind() == SyntaxKind::LBrace)
    );
}

#[test]
fn case_like_c7_handoffs_wrong_colon_body_indentation() {
    for (source, block_kind, arm_kind) in [
        (
            "case x:\ny -> z",
            SyntaxKind::CaseBlock,
            SyntaxKind::CaseArm,
        ),
        (
            "catch x:\ny -> z",
            SyntaxKind::CatchBlock,
            SyntaxKind::CatchArm,
        ),
    ] {
        let (green, exit) = run(source);
        let root = SyntaxNode::new_root(green);
        let block = root
            .descendants()
            .find(|node| node.kind() == block_kind)
            .expect("case-like block");
        assert_eq!(
            block
                .descendants()
                .filter(|node| node.kind() == arm_kind)
                .count(),
            1,
            "{source:?}"
        );
        assert_eq!(
            block
                .descendants()
                .filter(|node| node.kind() == SyntaxKind::Missing)
                .count(),
            1,
            "{source:?}"
        );
        assert!(
            !block
                .descendants_with_tokens()
                .filter_map(|element| element.into_token())
                .any(|token| token.text() == "y"),
            "{source:?}"
        );
        assert_handoff_identifier(&exit, "y");
    }
}

#[test]
fn case_like_c7_keeps_arm_sequences_inside_their_layout_region() {
    for (source, expression_kind, arm_kind, successor) in [
        (
            "case x: a -> b\nc -> d",
            SyntaxKind::CaseExpression,
            SyntaxKind::CaseArm,
            "c",
        ),
        (
            "catch x: a -> b\nc -> d",
            SyntaxKind::CatchExpression,
            SyntaxKind::CatchArm,
            "c",
        ),
        (
            "case x:\n  a -> b\nc -> d",
            SyntaxKind::CaseExpression,
            SyntaxKind::CaseArm,
            "c",
        ),
        (
            "catch x:\n  a -> b\nc -> d",
            SyntaxKind::CatchExpression,
            SyntaxKind::CatchArm,
            "c",
        ),
    ] {
        let (green, exit) = run(source);
        let root = SyntaxNode::new_root(green);
        let expression = expression(&root, expression_kind);
        assert_eq!(
            expression
                .descendants()
                .filter(|node| node.kind() == arm_kind)
                .count(),
            1,
            "{source:?}"
        );
        assert_handoff_identifier(&exit, successor);
    }

    for (source, expression_kind, arm_kind, separator_kind) in [
        (
            "case x:\n  a -> b,\nc -> d",
            SyntaxKind::CaseExpression,
            SyntaxKind::CaseArm,
            SyntaxKind::CaseArmSeparator,
        ),
        (
            "catch x:\n  a -> b,\nc -> d",
            SyntaxKind::CatchExpression,
            SyntaxKind::CatchArm,
            SyntaxKind::CatchArmSeparator,
        ),
    ] {
        let (green, exit) = run(source);
        let root = SyntaxNode::new_root(green);
        let expression = expression(&root, expression_kind);
        assert_eq!(
            expression
                .descendants()
                .filter(|node| node.kind() == arm_kind)
                .count(),
            1,
            "{source:?}"
        );
        assert_eq!(
            expression
                .descendants()
                .filter(|node| node.kind() == separator_kind)
                .count(),
            1,
            "{source:?}"
        );
        assert_handoff_identifier(&exit, "c");
    }
}

#[test]
fn case_like_c7_recovers_case_next_arm_at_its_following_separator() {
    let source = "case x: a -> b, @, c -> d";
    let (green, exit) = run(source);
    assert_eq!(green.to_string(), source);
    assert!(matches!(exit, Some(Err(Either::Right(_)))));

    let root = SyntaxNode::new_root(green);
    let case = expression(&root, SyntaxKind::CaseExpression);
    assert_eq!(
        case.descendants()
            .filter(|node| node.kind() == SyntaxKind::CaseArm)
            .count(),
        3
    );
    assert_eq!(
        case.descendants()
            .filter(|node| node.kind() == SyntaxKind::CaseArmSeparator)
            .count(),
        2
    );
    assert!(
        case.descendants_with_tokens()
            .filter_map(|element| element.into_token())
            .any(|token| token.kind() == SyntaxKind::Error && token.text() == "@")
    );
}

#[test]
fn case_like_c7_keeps_arm_entry_trivia_with_its_block() {
    let source = "case x:  a -> b,  _ -> c";
    let (green, exit) = run(source);
    assert_eq!(green.to_string(), source);
    assert!(matches!(exit, Some(Err(Either::Right(_)))));

    let root = SyntaxNode::new_root(green);
    let block = root
        .descendants()
        .find(|node| node.kind() == SyntaxKind::CaseBlock)
        .expect("CaseBlock");
    assert_eq!(
        block
            .children_with_tokens()
            .filter_map(|element| element.into_token())
            .filter(|token| token.kind() == SyntaxKind::Whitespace && token.text() == "  ")
            .count(),
        2
    );
}

fn case_like_literal_production(source: &str) -> SyntaxNode {
    let text: std::sync::Arc<crate::SourceText> = std::sync::Arc::from(source);
    let parsed = crate::parse_file(
        text.clone(),
        std::sync::Arc::new(crate::scan_header(text)),
        std::sync::Arc::new(crate::SyntaxEnvironment::empty()),
    );
    assert_eq!(parsed.green().to_string(), source);
    let diagnostics = parsed.syntax_diagnostics().unwrap();
    assert!(diagnostics.is_empty(), "{source:?}: {diagnostics:#?}");
    assert!(structural_facts(parsed.green()).is_empty(), "{source:?}");
    let root = SyntaxNode::new_root(parsed.green().clone());
    assert!(
        !root.descendants_with_tokens().any(|element| matches!(
            element.kind(),
            SyntaxKind::Error | SyntaxKind::Missing | SyntaxKind::Invalid
        )),
        "{source:?}"
    );
    root
}

#[test]
fn bare_quote_arm_rule_literals_were_already_accepted_before_wp8() {
    // Measured before the WP-8 parser change: both arm owners accepted the
    // bare quote and built the existing RuleLiteral CST without recovery.
    for (source, arm_kind) in [
        (
            "case source:\n    \"GET :resource\" -> resource",
            SyntaxKind::CaseArm,
        ),
        (
            "catch source:\n    \"GET :resource\" -> resource",
            SyntaxKind::CatchArm,
        ),
    ] {
        let root = case_like_literal_production(source);
        let arm = root
            .descendants()
            .find(|node| node.kind() == arm_kind)
            .expect("case-like arm");
        let literal = arm
            .descendants()
            .find(|node| node.kind() == SyntaxKind::RuleLiteral)
            .expect("arm RuleLiteral");
        assert_eq!(
            literal
                .descendants_with_tokens()
                .filter_map(|element| element.into_token())
                .find(|token| token.kind() == SyntaxKind::RuleLiteralStart)
                .map(|token| (token.kind(), token.text().to_owned())),
            Some((SyntaxKind::RuleLiteralStart, "\"".to_owned())),
            "{source:?}"
        );
    }
}

#[test]
fn non_quote_pattern_tilde_and_mid_pattern_tilde_quote_keep_pre_wp8_recovery() {
    for (source, expected_facts, expected_errors) in [
        (
            "case source:\n    ~name -> 1",
            vec![(StructuralKind::ErrorGroup, 17..18)],
            vec!["~"],
        ),
        (
            "case source:\n    x ~\"a\" -> 1",
            vec![
                (StructuralKind::Missing, 19..19),
                (StructuralKind::ErrorGroup, 19..20),
                (StructuralKind::ErrorGroup, 24..28),
            ],
            vec!["~", "-", ">", " ", "1"],
        ),
    ] {
        let text: std::sync::Arc<crate::SourceText> = std::sync::Arc::from(source);
        let parsed = crate::parse_file(
            text.clone(),
            std::sync::Arc::new(crate::scan_header(text)),
            std::sync::Arc::new(crate::SyntaxEnvironment::empty()),
        );
        let root = SyntaxNode::new_root(parsed.green().clone());
        assert_eq!(
            structural_facts(parsed.green()),
            expected_facts,
            "{source:?}"
        );
        assert_eq!(
            root.descendants_with_tokens()
                .filter_map(|element| element.into_token())
                .filter(|token| token.kind() == SyntaxKind::Error)
                .map(|token| token.text().to_owned())
                .collect::<Vec<_>>(),
            expected_errors,
            "{source:?}"
        );
        assert!(
            !root
                .descendants()
                .any(|node| node.kind() == SyntaxKind::RuleLiteral),
            "{source:?}"
        );
    }
}

#[test]
fn tilde_quote_rule_literal_patterns_parse_in_case_and_catch_multi_arm_blocks() {
    for (source, arm_kind) in [
        (
            "case source:\n    ~\"GET :resource/{tail = ..}\" -> resource\n    _ -> \"no match\"",
            SyntaxKind::CaseArm,
        ),
        (
            "catch source:\n    ~\"GET :resource/{tail = ..}\" -> resource\n    _ -> \"no match\"",
            SyntaxKind::CatchArm,
        ),
    ] {
        let root = case_like_literal_production(source);
        let arms = root
            .descendants()
            .filter(|node| node.kind() == arm_kind)
            .collect::<Vec<_>>();
        assert_eq!(arms.len(), 2, "{source:?}");
        let literal = arms[0]
            .descendants()
            .find(|node| node.kind() == SyntaxKind::RuleLiteral)
            .expect("parser-pattern RuleLiteral");
        assert_eq!(
            literal
                .descendants_with_tokens()
                .filter_map(|element| element.into_token())
                .find(|token| token.kind() == SyntaxKind::RuleLiteralStart)
                .map(|token| (token.kind(), token.text().to_owned())),
            Some((SyntaxKind::RuleLiteralStart, "~\"".to_owned())),
            "{source:?}"
        );
        assert_eq!(
            literal
                .descendants()
                .filter(|node| node.kind() == SyntaxKind::RuleLazyCapture)
                .count(),
            1,
            "{source:?}"
        );
        assert_eq!(
            literal
                .descendants()
                .filter(|node| node.kind() == SyntaxKind::RuleCapture)
                .count(),
            1,
            "{source:?}"
        );
    }
}

#[test]
fn tilde_quote_rule_literal_pattern_guards_remain_direct_arm_children() {
    for (source, arm_kind, guard_kind) in [
        (
            "case source:\n    ~\"a\" if c -> 1",
            SyntaxKind::CaseArm,
            SyntaxKind::CaseGuard,
        ),
        (
            "case source:\n    ~\"a\" where c -> 1",
            SyntaxKind::CaseArm,
            SyntaxKind::CaseGuard,
        ),
        (
            "catch source:\n    ~\"a\" if c -> 1",
            SyntaxKind::CatchArm,
            SyntaxKind::CatchGuard,
        ),
        (
            "catch source:\n    ~\"a\" where c -> 1",
            SyntaxKind::CatchArm,
            SyntaxKind::CatchGuard,
        ),
    ] {
        let root = case_like_literal_production(source);
        let arm = root
            .descendants()
            .find(|node| node.kind() == arm_kind)
            .expect("case-like arm");
        assert_eq!(
            arm.children()
                .filter(|node| node.kind() == guard_kind)
                .count(),
            1,
            "{source:?}"
        );
        assert_eq!(
            arm.descendants()
                .find(|node| node.kind() == SyntaxKind::RuleLiteral)
                .expect("guarded parser-pattern RuleLiteral")
                .to_string(),
            "~\"a\"",
            "{source:?}"
        );
    }
}

#[test]
fn tilde_quote_arm_rule_literals_reuse_expression_multiline_scanning() {
    let source = "case source:\n    ~\"GET\r\n    :resource\" -> resource";
    let root = case_like_literal_production(source);
    let literal = root
        .descendants()
        .find(|node| node.kind() == SyntaxKind::RuleLiteral)
        .expect("multiline arm RuleLiteral");
    assert_eq!(literal.to_string(), "~\"GET\r\n    :resource\"");
    assert_eq!(
        literal
            .first_token()
            .map(|token| (token.kind(), token.text().to_owned())),
        Some((SyntaxKind::RuleLiteralStart, "~\"".to_owned()))
    );
    assert_eq!(
        literal
            .descendants()
            .filter(|node| node.kind() == SyntaxKind::RuleLazyCapture)
            .count(),
        1
    );
}

#[test]
fn expression_rule_literal_positions_keep_pre_wp8_behavior() {
    for source in ["my x = ~\"a\"", "case ~\"a\":\n    _ -> 1"] {
        let root = case_like_literal_production(source);
        let literal = root
            .descendants()
            .find(|node| node.kind() == SyntaxKind::RuleLiteral)
            .expect("expression RuleLiteral");
        assert_eq!(
            literal
                .descendants_with_tokens()
                .filter_map(|element| element.into_token())
                .find(|token| token.kind() == SyntaxKind::RuleLiteralStart)
                .map(|token| (token.kind(), token.text().to_owned())),
            Some((SyntaxKind::RuleLiteralStart, "~\"".to_owned())),
            "{source:?}"
        );
        assert_eq!(
            literal.parent().map(|node| node.kind()),
            Some(SyntaxKind::OperatorChain),
            "{source:?}"
        );
    }

    // An expression RuleLiteral is a NUD form, not an ML argument after a
    // complete primary. WP-8 changes only Pattern NUD admission.
    let source = "f ~\"a\"";
    let text: std::sync::Arc<crate::SourceText> = std::sync::Arc::from(source);
    let parsed = crate::parse_file(
        text.clone(),
        std::sync::Arc::new(crate::scan_header(text)),
        std::sync::Arc::new(crate::SyntaxEnvironment::empty()),
    );
    let root = SyntaxNode::new_root(parsed.green().clone());
    assert_eq!(
        structural_facts(parsed.green()),
        [(StructuralKind::ErrorGroup, 2..6)]
    );
    assert!(
        !root
            .descendants()
            .any(|node| node.kind() == SyntaxKind::RuleLiteral)
    );
}

#[test]
fn case_like_label_probe_wins_before_label_expression_scrutinees() {
    let operators = OperatorTable::from_declarations([
        OperatorDeclaration::new(
            "-",
            OperatorFixities::new()
                .with_infix(BindingPower::scalar(40), BindingPower::new(40, [1])),
        ),
        OperatorDeclaration::new(
            ">",
            OperatorFixities::new()
                .with_infix(BindingPower::scalar(30), BindingPower::new(30, [1])),
        ),
    ])
    .expect("arithmetic operators used inside the label recursion examples");
    for (source, expression_kind, label_kind, scrutinee_kind, arm_kind, spelling) in [
        (
            "case 'count 3:\n    0 -> 1\n    n -> 'count (n - 1)",
            SyntaxKind::CaseExpression,
            SyntaxKind::CaseLabel,
            SyntaxKind::CaseScrutinee,
            SyntaxKind::CaseArm,
            "'count",
        ),
        (
            "catch 'again 3:\n    n if n > 0 -> 'again (n - 1)\n    n -> n",
            SyntaxKind::CatchExpression,
            SyntaxKind::CatchLabel,
            SyntaxKind::CatchScrutinee,
            SyntaxKind::CatchArm,
            "'again",
        ),
    ] {
        let (green, exit) = run_with(source, &operators);
        assert_eq!(green.to_string(), source, "{source:?}");
        assert!(matches!(exit, Some(Err(Either::Right(_)))), "{source:?}");
        assert!(structural_facts(&green).is_empty(), "{source:?}");
        let root = SyntaxNode::new_root(green);
        assert!(
            !root.descendants_with_tokens().any(|element| matches!(
                element.kind(),
                SyntaxKind::Error | SyntaxKind::Missing | SyntaxKind::Invalid
            )),
            "{source:?}"
        );
        let expression = root
            .descendants()
            .find(|node| node.kind() == expression_kind)
            .expect("case-like expression");
        assert_eq!(
            expression
                .children()
                .map(|node| node.kind())
                .collect::<Vec<_>>(),
            [
                label_kind,
                scrutinee_kind,
                match expression_kind {
                    SyntaxKind::CaseExpression => SyntaxKind::CaseBlock,
                    SyntaxKind::CatchExpression => SyntaxKind::CatchBlock,
                    _ => unreachable!(),
                },
            ],
            "{source:?}"
        );
        assert_eq!(
            expression
                .descendants()
                .filter(|node| node.kind() == arm_kind)
                .count(),
            2,
            "{source:?}"
        );

        let labels = expression
            .descendants_with_tokens()
            .filter_map(|element| element.into_token())
            .filter(|token| token.kind() == SyntaxKind::SigilIdentifier && token.text() == spelling)
            .collect::<Vec<_>>();
        assert_eq!(labels.len(), 2, "{source:?}");
        assert_eq!(
            labels
                .iter()
                .map(|token| token.parent().expect("label token parent").kind())
                .collect::<Vec<_>>(),
            [label_kind, SyntaxKind::IdentifierExpression],
            "{source:?}"
        );

        let scrutinee = expression
            .children()
            .find(|node| node.kind() == scrutinee_kind)
            .expect("case-like scrutinee");
        assert!(
            !scrutinee
                .descendants_with_tokens()
                .any(|element| element.kind() == SyntaxKind::SigilIdentifier),
            "{source:?}"
        );
        assert_eq!(
            scrutinee
                .descendants()
                .filter(|node| node.kind() == SyntaxKind::IntegerLiteral)
                .count(),
            1,
            "{source:?}"
        );
    }
}

fn assert_case_like_string_scrutinee(root: &SyntaxNode, scrutinee_kind: SyntaxKind, width: usize) {
    let scrutinee = expression(root, scrutinee_kind);
    let children = scrutinee.children().collect::<Vec<_>>();
    assert_eq!(children.len(), 1);
    assert_eq!(children[0].kind(), SyntaxKind::OperatorChain);
    let literals = scrutinee
        .descendants()
        .filter(|node| node.kind() == SyntaxKind::StringLiteral)
        .collect::<Vec<_>>();
    assert_eq!(literals.len(), 1);
    assert_eq!(literals[0].parent(), Some(children[0].clone()));
    let delimiters = literals[0]
        .children_with_tokens()
        .filter_map(|element| element.into_token())
        .filter(|token| {
            matches!(
                token.kind(),
                SyntaxKind::StringStart | SyntaxKind::StringEnd
            )
        })
        .collect::<Vec<_>>();
    assert_eq!(delimiters.len(), 2);
    assert_eq!(delimiters[0].kind(), SyntaxKind::StringStart);
    assert_eq!(delimiters[1].kind(), SyntaxKind::StringEnd);
    let delimiter = "\"".repeat(width);
    assert_eq!(delimiters[0].text(), delimiter);
    assert_eq!(delimiters[1].text(), delimiter);
    let interior = usize::from(delimiters[0].text_range().end())
        ..usize::from(delimiters[1].text_range().start());
    assert_eq!(&root.to_string()[interior], r" a\nb ");
}

#[test]
fn case_like_literal_heads_preserve_normal_and_heredoc_scrutinees() {
    for (prefix, scrutinee_kind, label_kind, labeled, finish) in [
        (
            "case",
            SyntaxKind::CaseScrutinee,
            SyntaxKind::CaseLabel,
            false,
            ": value -> value",
        ),
        (
            "case 'go",
            SyntaxKind::CaseScrutinee,
            SyntaxKind::CaseLabel,
            true,
            ": value -> value",
        ),
        (
            "catch",
            SyntaxKind::CatchScrutinee,
            SyntaxKind::CatchLabel,
            false,
            " { value -> value }",
        ),
        (
            "catch 'go",
            SyntaxKind::CatchScrutinee,
            SyntaxKind::CatchLabel,
            true,
            " { value -> value }",
        ),
    ] {
        for width in [1, 3, 4] {
            let delimiter = "\"".repeat(width);
            let source = format!("{prefix} {delimiter} a\\nb {delimiter}{finish}");
            let root = case_like_literal_production(&source);
            assert_case_like_string_scrutinee(&root, scrutinee_kind, width);
            let labels = root
                .descendants()
                .filter(|node| node.kind() == label_kind)
                .collect::<Vec<_>>();
            assert_eq!(labels.len(), usize::from(labeled), "{source:?}");
            if labeled {
                assert!(matches!(
                    labels[0].parent().unwrap().kind(),
                    SyntaxKind::CaseExpression | SyntaxKind::CatchExpression
                ));
            }
        }
    }
}

#[test]
fn case_like_literal_heads_preserve_rule_literal_openers() {
    for (prefix, scrutinee_kind, label_kind, labeled, finish) in [
        (
            "case",
            SyntaxKind::CaseScrutinee,
            SyntaxKind::CaseLabel,
            false,
            ": value -> value",
        ),
        (
            "case 'go",
            SyntaxKind::CaseScrutinee,
            SyntaxKind::CaseLabel,
            true,
            ": value -> value",
        ),
        (
            "catch",
            SyntaxKind::CatchScrutinee,
            SyntaxKind::CatchLabel,
            false,
            " { value -> value }",
        ),
        (
            "catch 'go",
            SyntaxKind::CatchScrutinee,
            SyntaxKind::CatchLabel,
            true,
            " { value -> value }",
        ),
    ] {
        let source = format!("{prefix} ~\"abc\"{finish}");
        let root = case_like_literal_production(&source);
        let scrutinee = expression(&root, scrutinee_kind);
        let chain = scrutinee.children().collect::<Vec<_>>();
        assert_eq!(chain.len(), 1);
        assert_eq!(chain[0].kind(), SyntaxKind::OperatorChain);
        let literals = scrutinee
            .descendants()
            .filter(|node| node.kind() == SyntaxKind::RuleLiteral)
            .collect::<Vec<_>>();
        assert_eq!(literals.len(), 1);
        assert_eq!(literals[0].parent(), Some(chain[0].clone()));
        let tokens = literals[0]
            .descendants_with_tokens()
            .filter_map(|element| element.into_token())
            .filter(|token| {
                matches!(
                    token.kind(),
                    SyntaxKind::RuleLiteralStart
                        | SyntaxKind::RuleLiteralText
                        | SyntaxKind::RuleLiteralEnd
                )
            })
            .map(|token| (token.kind(), token.text().to_owned()))
            .collect::<Vec<_>>();
        assert_eq!(
            tokens,
            [
                (SyntaxKind::RuleLiteralStart, "~\"".to_owned()),
                (SyntaxKind::RuleLiteralText, "abc".to_owned()),
                (SyntaxKind::RuleLiteralEnd, "\"".to_owned()),
            ]
        );
        assert_eq!(
            root.descendants()
                .filter(|node| node.kind() == label_kind)
                .count(),
            usize::from(labeled)
        );
    }
}

#[test]
fn case_like_literal_head_in_binding_preserves_exact_catch_heredoc() {
    let source = r#"my main = catch """ a\nb """ { value -> value }"#;
    let root = case_like_literal_production(source);
    assert_case_like_string_scrutinee(&root, SyntaxKind::CatchScrutinee, 3);
    assert_eq!(
        root.descendants()
            .filter(|node| node.kind() == SyntaxKind::CatchLabel)
            .count(),
        0
    );
}
