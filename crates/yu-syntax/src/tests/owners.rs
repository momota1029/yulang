use crate::tests::support::*;

fn assert_ml_children(node: &SyntaxNode, expected: &[(SyntaxKind, std::ops::Range<usize>)]) {
    let actual = node
        .children_with_tokens()
        .map(|child| {
            let range = child.text_range();
            (
                child.kind(),
                usize::from(range.start())..usize::from(range.end()),
            )
        })
        .collect::<Vec<_>>();
    assert_eq!(actual, expected, "{node:?}");
}

#[test]
fn ml_separator_leading_is_direct_outer_chain_content() {
    for source in ["f x y", "apply left right", "関数 引数 次"] {
        let (green, exit) = run(source);
        assert_eq!(green.to_string(), source);
        assert!(matches!(exit, Some(Err(Either::Right(_)))));
        let root = SyntaxNode::new_root(green);
        let chain = root.children().next().unwrap();
        let first_space = source.find(' ').unwrap();
        let last_space = source.rfind(' ').unwrap();
        assert_ml_children(
            &chain,
            &[
                (SyntaxKind::IdentifierExpression, 0..first_space),
                (SyntaxKind::Whitespace, first_space..first_space + 1),
                (SyntaxKind::MlArgument, first_space + 1..last_space),
                (SyntaxKind::Whitespace, last_space..last_space + 1),
                (SyntaxKind::MlArgument, last_space + 1..source.len()),
            ],
        );
        for argument in chain
            .children()
            .filter(|node| node.kind() == SyntaxKind::MlArgument)
        {
            let range = argument.text_range();
            let range = usize::from(range.start())..usize::from(range.end());
            assert_ml_children(&argument, &[(SyntaxKind::OperatorChain, range.clone())]);
            assert_ml_children(
                &argument.children().next().unwrap(),
                &[(SyntaxKind::IdentifierExpression, range)],
            );
        }
    }
}

#[test]
fn ml_argument_forms_keep_separator_outside_payload() {
    for payload in ["{ x }", "(x)", "42", "\"text\""] {
        for separator in [" ", " /* gap */ ", "\n  "] {
            let source = format!("f{separator}{payload}");
            let (green, exit) = run(&source);
            assert_eq!(green.to_string(), source);
            assert!(matches!(exit, Some(Err(Either::Right(_)))));
            let root = SyntaxNode::new_root(green);
            let chain = root.children().next().unwrap();
            let start = 1 + separator.len();
            let mut expected = vec![(SyntaxKind::IdentifierExpression, 0..1)];
            expected.extend(match separator {
                " " => vec![(SyntaxKind::Whitespace, 1..2)],
                " /* gap */ " => vec![
                    (SyntaxKind::Whitespace, 1..2),
                    (SyntaxKind::BlockComment, 2..11),
                    (SyntaxKind::Whitespace, 11..12),
                ],
                _ => vec![(SyntaxKind::Newline, 1..2), (SyntaxKind::Whitespace, 2..4)],
            });
            expected.push((SyntaxKind::MlArgument, start..source.len()));
            assert_ml_children(&chain, &expected);
            let argument = chain
                .children()
                .find(|node| node.kind() == SyntaxKind::MlArgument)
                .unwrap();
            assert_ml_children(
                &argument,
                &[(SyntaxKind::OperatorChain, start..source.len())],
            );
            assert!(!argument.descendants_with_tokens().any(|element| matches!(
                element.kind(),
                SyntaxKind::Missing | SyntaxKind::Error | SyntaxKind::Invalid
            )));
        }
    }
}

#[test]
fn ml_normalized_quote_separator_stays_in_outer_chain() {
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
    let source = "> > f\n> >   x\n> > ```\nouter";
    let (green, exit, remainder) = run_normalized(
        source,
        &OperatorTable::empty(),
        500,
        LineEntry::PhysicalStart,
        Some(&fence),
    );
    let Some(NormalizedExit::Complete(Err(Either::Left(boundary)), LineEntry::PhysicalStart)) =
        exit
    else {
        panic!("ML must retain the exact fence handoff");
    };
    assert!(boundary.payload_view().is_boundary());
    assert_eq!(remainder, "> > ```\nouter");
    assert_eq!(green.to_string(), "> > f\n> >   x");
    let root = SyntaxNode::new_root(green);
    let chain = root.children().next().unwrap();
    assert_ml_children(
        &chain,
        &[
            (SyntaxKind::IdentifierExpression, 0..5),
            (SyntaxKind::Newline, 5..6),
            (SyntaxKind::YmQuotePrefix, 6..10),
            (SyntaxKind::Whitespace, 10..12),
            (SyntaxKind::MlArgument, 12..13),
        ],
    );
    let argument = chain
        .children()
        .find(|node| node.kind() == SyntaxKind::MlArgument)
        .unwrap();
    assert_ml_children(&argument, &[(SyntaxKind::OperatorChain, 12..13)]);
}

#[test]
fn ml_malformed_child_keeps_recovery_and_caller_successor() {
    for (source, offset) in [("f (", 0), ("x[f (]", 2)] {
        let (green, exit, remainder) =
            run_normalized(source, &OperatorTable::empty(), 0, LineEntry::InLine, None);
        assert_eq!(green.to_string(), source);
        assert_eq!(remainder, "");
        assert!(matches!(
            exit,
            Some(NormalizedExit::Complete(Err(Either::Right(_)), _))
        ));
        let root = SyntaxNode::new_root(green);
        let chain = root
            .descendants()
            .find(|node| {
                node.kind() == SyntaxKind::OperatorChain
                    && node
                        .children()
                        .any(|child| child.kind() == SyntaxKind::MlArgument)
            })
            .unwrap();
        assert_ml_children(
            &chain,
            &[
                (SyntaxKind::IdentifierExpression, offset..offset + 1),
                (SyntaxKind::Whitespace, offset + 1..offset + 2),
                (SyntaxKind::MlArgument, offset + 2..offset + 3),
            ],
        );
        let argument = chain
            .children()
            .find(|node| node.kind() == SyntaxKind::MlArgument)
            .unwrap();
        assert_ml_children(
            &argument,
            &[(SyntaxKind::OperatorChain, offset + 2..offset + 3)],
        );
        let group = argument
            .descendants()
            .find(|node| node.kind() == SyntaxKind::ParenthesizedExpression)
            .unwrap();
        assert_ml_children(
            &group,
            &[
                (SyntaxKind::LParen, offset + 2..offset + 3),
                (SyntaxKind::Missing, offset + 3..offset + 3),
            ],
        );
        if offset != 0 {
            let close = root
                .descendants_with_tokens()
                .find(|element| element.kind() == SyntaxKind::RBracket)
                .unwrap()
                .into_token()
                .unwrap();
            assert_eq!(close.parent().unwrap().kind(), SyntaxKind::IndexTail);
            assert_eq!(
                close.text_range(),
                rowan::TextRange::new(5.into(), 6.into())
            );
        }
    }
}

#[test]
fn parenthesized_primary_owns_its_sequence_and_outer_ml_tail() {
    let source = "(a,b;c) d";
    let (green, exit) = run(source);
    assert_eq!(green.to_string(), source);
    assert!(matches!(exit, Some(Err(Either::Right(_)))));

    let root = SyntaxNode::new_root(green);
    let outer = root
        .children()
        .find(|node| node.kind() == SyntaxKind::OperatorChain)
        .expect("outer expression chain");
    let group = outer
        .children()
        .find(|node| node.kind() == SyntaxKind::ParenthesizedExpression)
        .expect("parenthesized primary");
    assert_eq!(
        group
            .children()
            .filter(|node| node.kind() == SyntaxKind::OperatorChain)
            .count(),
        3
    );
    assert_eq!(
        outer
            .children()
            .filter(|node| node.kind() == SyntaxKind::MlArgument)
            .count(),
        1
    );
    assert_eq!(
        root.descendants_with_tokens()
            .filter_map(|element| element.into_token())
            .map(|token| token.kind())
            .collect::<Vec<_>>(),
        [
            SyntaxKind::LParen,
            SyntaxKind::Identifier,
            SyntaxKind::Comma,
            SyntaxKind::Identifier,
            SyntaxKind::Error,
            SyntaxKind::Identifier,
            SyntaxKind::RParen,
            SyntaxKind::Whitespace,
            SyntaxKind::Identifier,
        ]
    );
    // Parenthesized expressions accept comma but not semicolon.  The sequence
    // and outer ML ownership stay unchanged while the local separator recovers.
    assert_eq!(
        crate::tests::recovery_output::recovery_groups(&group)
            .into_iter()
            .filter(|run| run.parent().as_ref() == Some(&group))
            .count(),
        1
    );
    assert!(
        !root
            .descendants()
            .any(|node| node.kind() == SyntaxKind::Missing)
    );
}

#[test]
fn call_and_index_own_valid_multiple_item_sequences() {
    let source = "f(a,b;c)[x,y;z]";
    let (green, exit) = run(source);
    assert_eq!(green.to_string(), source);
    assert!(matches!(exit, Some(Err(Either::Right(_)))));

    let root = SyntaxNode::new_root(green);
    let outer = root
        .children()
        .find(|node| node.kind() == SyntaxKind::OperatorChain)
        .expect("outer expression chain");
    let call = outer
        .children()
        .find(|node| node.kind() == SyntaxKind::CallTail)
        .expect("call tail");
    assert_eq!(
        call.children()
            .filter(|node| node.kind() == SyntaxKind::OperatorChain)
            .count(),
        3
    );
    let index = outer
        .children()
        .find(|node| node.kind() == SyntaxKind::IndexTail)
        .expect("index tail");
    assert_eq!(
        index
            .children()
            .filter(|node| node.kind() == SyntaxKind::IndexItem)
            .count(),
        3
    );
    let rparen = root
        .descendants_with_tokens()
        .filter_map(|element| element.into_token())
        .find(|token| token.kind() == SyntaxKind::RParen)
        .expect("call close");
    assert_eq!(
        rparen.parent().expect("call close owner").kind(),
        SyntaxKind::CallTail
    );
    let rbracket = root
        .descendants_with_tokens()
        .filter_map(|element| element.into_token())
        .find(|token| token.kind() == SyntaxKind::RBracket)
        .expect("index close");
    assert_eq!(
        rbracket.parent().expect("index close owner").kind(),
        SyntaxKind::IndexTail
    );
    assert!(!root.descendants_with_tokens().any(|node| matches!(
        node.kind(),
        SyntaxKind::Missing | SyntaxKind::Error | SyntaxKind::Invalid
    )));
}

#[test]
fn each_delimited_owner_accepts_an_empty_valid_sequence() {
    for (source, owner) in [
        ("()", SyntaxKind::ParenthesizedExpression),
        ("f()", SyntaxKind::CallTail),
        ("x[]", SyntaxKind::IndexTail),
    ] {
        let (green, exit) = run(source);
        assert_eq!(green.to_string(), source, "{source:?}");
        assert!(matches!(exit, Some(Err(Either::Right(_)))), "{source:?}");

        let root = SyntaxNode::new_root(green);
        let node = root
            .descendants()
            .find(|node| node.kind() == owner)
            .expect("delimited owner");
        assert_eq!(
            node.children()
                .filter(|node| matches!(
                    node.kind(),
                    SyntaxKind::OperatorChain | SyntaxKind::IndexItem
                ))
                .count(),
            0,
            "{source:?}"
        );
    }
}

#[test]
fn delimited_owner_emits_missing_close_before_handing_eof_outward() {
    for (source, owner) in [
        ("(a", SyntaxKind::ParenthesizedExpression),
        ("f(a /* tail */", SyntaxKind::CallTail),
        ("x[a", SyntaxKind::IndexTail),
        ("a.(x", SyntaxKind::ProjectionTupleTail),
        ("a.{x", SyntaxKind::ProjectionRecordTail),
    ] {
        let (green, exit) = run(source);
        assert_eq!(green.to_string(), source, "{source:?}");
        assert!(matches!(exit, Some(Err(Either::Right(_)))), "{source:?}");

        let root = SyntaxNode::new_root(green);
        let owner = root
            .descendants()
            .find(|node| node.kind() == owner)
            .expect("delimited owner");
        assert_eq!(
            owner.children().last().map(|node| node.kind()),
            Some(SyntaxKind::Missing),
            "{source:?}"
        );
        assert!(
            !root
                .descendants_with_tokens()
                .any(|node| matches!(node.kind(), SyntaxKind::Error | SyntaxKind::Invalid)),
            "{source:?}"
        );
    }
}

#[test]
fn delimited_owner_recovers_missing_items_before_separators() {
    for (source, owner) in [
        ("(,a)", SyntaxKind::ParenthesizedExpression),
        ("f(,a)", SyntaxKind::CallTail),
        ("f(a,,b)", SyntaxKind::CallTail),
        ("x[,a]", SyntaxKind::IndexTail),
        ("a.(,x)", SyntaxKind::ProjectionTupleTail),
        ("a.{,x}", SyntaxKind::ProjectionRecordTail),
    ] {
        let (green, exit) = run(source);
        assert_eq!(green.to_string(), source, "{source:?}");
        assert!(matches!(exit, Some(Err(Either::Right(_)))), "{source:?}");

        let root = SyntaxNode::new_root(green);
        let owner = root
            .descendants()
            .find(|node| node.kind() == owner)
            .expect("delimited owner");
        assert_eq!(
            owner
                .children()
                .filter(|node| node.kind() == SyntaxKind::Missing)
                .count(),
            1,
            "{source:?}"
        );
        assert!(
            !root
                .descendants_with_tokens()
                .any(|node| matches!(node.kind(), SyntaxKind::Error | SyntaxKind::Invalid)),
            "{source:?}"
        );
    }
}

#[test]
fn delimited_nud_recovery_retries_one_maximal_error_run() {
    for (source, owner, item_kind) in [
        (
            "(@@a)",
            SyntaxKind::ParenthesizedExpression,
            SyntaxKind::OperatorChain,
        ),
        ("f(@a)", SyntaxKind::CallTail, SyntaxKind::OperatorChain),
        ("x[@a]", SyntaxKind::IndexTail, SyntaxKind::IndexItem),
        (
            "a.(@x)",
            SyntaxKind::ProjectionTupleTail,
            SyntaxKind::OperatorChain,
        ),
        (
            "a.{@x}",
            SyntaxKind::ProjectionRecordTail,
            SyntaxKind::OperatorChain,
        ),
    ] {
        let (green, exit) = run(source);
        assert_eq!(green.to_string(), source, "{source:?}");
        assert!(matches!(exit, Some(Err(Either::Right(_)))), "{source:?}");

        let root = SyntaxNode::new_root(green);
        let owner = root
            .descendants()
            .find(|node| node.kind() == owner)
            .expect("delimited owner");
        assert_eq!(
            crate::tests::recovery_output::recovery_groups(&owner)
                .into_iter()
                .filter(|group| group.parent().as_ref() == Some(&owner))
                .count(),
            1,
            "{source:?}"
        );
        assert_eq!(
            owner
                .children()
                .filter(|node| node.kind() == item_kind)
                .count(),
            1,
            "{source:?}"
        );
        assert!(
            !owner
                .descendants()
                .any(|node| node.kind() == SyntaxKind::Missing),
            "{source:?}"
        );
    }
}

#[test]
fn delimited_owner_consumes_wrong_closes_before_settling_its_own_close() {
    for (source, owner, wrong, missing) in [
        (
            "(a]",
            SyntaxKind::ParenthesizedExpression,
            SyntaxKind::RBracket,
            true,
        ),
        ("f(a])", SyntaxKind::CallTail, SyntaxKind::RBracket, false),
        ("x[a)", SyntaxKind::IndexTail, SyntaxKind::RParen, true),
        (
            "a.(x]",
            SyntaxKind::ProjectionTupleTail,
            SyntaxKind::RBracket,
            true,
        ),
        (
            "a.{x)",
            SyntaxKind::ProjectionRecordTail,
            SyntaxKind::RParen,
            true,
        ),
    ] {
        let (green, exit) = run(source);
        assert_eq!(green.to_string(), source, "{source:?}");
        assert!(matches!(exit, Some(Err(Either::Right(_)))), "{source:?}");

        let root = SyntaxNode::new_root(green);
        let owner = root
            .descendants()
            .find(|node| node.kind() == owner)
            .expect("delimited owner");
        let error = crate::tests::recovery_output::recovery_groups(&owner)
            .into_iter()
            .find(|group| group.parent().as_ref() == Some(&owner))
            .expect("owner-local wrong-close error");
        assert_eq!(
            error.first_token().map(|token| token.kind()),
            Some(SyntaxKind::Error),
            "{source:?}"
        );
        assert_eq!(
            error.text(),
            if wrong == SyntaxKind::RBracket {
                "]"
            } else {
                ")"
            }
        );
        assert_eq!(
            owner
                .children()
                .any(|node| node.kind() == SyntaxKind::Missing),
            missing,
            "{source:?}"
        );
    }
}

#[test]
fn parenthesized_items_recover_a_same_line_missing_separator_without_ml() {
    let (green, exit) = run("(a b)");
    assert_eq!(green.to_string(), "(a b)");
    assert!(matches!(exit, Some(Err(Either::Right(_)))));

    let root = SyntaxNode::new_root(green);
    let group = root
        .descendants()
        .find(|node| node.kind() == SyntaxKind::ParenthesizedExpression)
        .expect("parenthesized expression");
    assert_eq!(
        group
            .children()
            .filter(|node| node.kind() == SyntaxKind::OperatorChain)
            .count(),
        2
    );
    assert_eq!(
        group
            .children()
            .filter(|node| node.kind() == SyntaxKind::Missing)
            .count(),
        1
    );
    assert_eq!(
        group
            .descendants()
            .filter(|node| node.kind() == SyntaxKind::MlArgument)
            .count(),
        0
    );
}

#[test]
fn block_comment_internal_newlines_are_not_parenthesized_layout() {
    let source = "(a /* outer\n inner */ b)";
    let (green, exit) = run(source);
    assert_eq!(green.to_string(), source);
    assert!(matches!(exit, Some(Err(Either::Right(_)))));

    let root = SyntaxNode::new_root(green);
    let group = root
        .descendants()
        .find(|node| node.kind() == SyntaxKind::ParenthesizedExpression)
        .expect("parenthesized expression");
    assert_eq!(
        group
            .children()
            .filter(|node| node.kind() == SyntaxKind::OperatorChain)
            .count(),
        2
    );
    assert_eq!(
        group
            .children()
            .filter(|node| node.kind() == SyntaxKind::Missing)
            .count(),
        1
    );
    assert!(
        !group
            .descendants()
            .any(|node| node.kind() == SyntaxKind::MlArgument)
    );
}

#[test]
fn delimited_items_accept_baseline_newlines_without_rescanning_the_handoff() {
    for (source, owner, item_kind) in [
        (
            "(a\nb)",
            SyntaxKind::ParenthesizedExpression,
            SyntaxKind::OperatorChain,
        ),
        ("f(a\nb)", SyntaxKind::CallTail, SyntaxKind::OperatorChain),
        ("x[a\nb]", SyntaxKind::IndexTail, SyntaxKind::IndexItem),
        (
            "a.(x\ny)",
            SyntaxKind::ProjectionTupleTail,
            SyntaxKind::OperatorChain,
        ),
        (
            "a.{x\ny}",
            SyntaxKind::ProjectionRecordTail,
            SyntaxKind::OperatorChain,
        ),
    ] {
        let (green, exit) = run(source);
        assert_eq!(green.to_string(), source, "{source:?}");
        assert!(matches!(exit, Some(Err(Either::Right(_)))), "{source:?}");

        let root = SyntaxNode::new_root(green);
        let owner = root
            .descendants()
            .find(|node| node.kind() == owner)
            .expect("delimited owner");
        assert_eq!(
            owner
                .children()
                .filter(|node| node.kind() == item_kind)
                .count(),
            2,
            "{source:?}"
        );
        assert!(
            !owner
                .descendants()
                .any(|node| node.kind() == SyntaxKind::Missing),
            "{source:?}"
        );
    }
}

#[test]
fn deeper_newlines_continue_the_current_delimited_item_chain() {
    for (source, owner, item_kind) in [
        (
            "(a\n  b)",
            SyntaxKind::ParenthesizedExpression,
            SyntaxKind::OperatorChain,
        ),
        ("f(a\n  b)", SyntaxKind::CallTail, SyntaxKind::OperatorChain),
        ("x[a\n  b]", SyntaxKind::IndexTail, SyntaxKind::IndexItem),
        (
            "a.(x\n  y)",
            SyntaxKind::ProjectionTupleTail,
            SyntaxKind::OperatorChain,
        ),
        (
            "a.{x\n  y}",
            SyntaxKind::ProjectionRecordTail,
            SyntaxKind::OperatorChain,
        ),
    ] {
        let (green, exit) = run(source);
        assert_eq!(green.to_string(), source, "{source:?}");
        assert!(matches!(exit, Some(Err(Either::Right(_)))), "{source:?}");

        let root = SyntaxNode::new_root(green);
        let owner = root
            .descendants()
            .find(|node| node.kind() == owner)
            .expect("delimited owner");
        assert_eq!(
            owner
                .children()
                .filter(|node| node.kind() == item_kind)
                .count(),
            1,
            "{source:?}"
        );
        assert_eq!(
            owner
                .descendants()
                .filter(|node| node.kind() == SyntaxKind::MlArgument)
                .count(),
            1,
            "{source:?}"
        );
        assert!(
            !owner.descendants_with_tokens().any(|node| matches!(
                node.kind(),
                SyntaxKind::Missing | SyntaxKind::Error | SyntaxKind::Invalid
            )),
            "{source:?}"
        );
    }
}

#[test]
fn record_projection_spread_owns_exact_marker_and_rhs() {
    let source = "a.{left, ..rest, right}";
    let operators = OperatorTable::from_declarations([OperatorDeclaration::new(
        "..",
        OperatorFixities::new().with_prefix(BindingPower::scalar(70)),
    )])
    .expect("a direct parser operator table");
    let (green, exit) = run_with(source, &operators);
    assert_eq!(green.to_string(), source);
    assert!(matches!(exit, Some(Err(Either::Right(_)))));

    let root = SyntaxNode::new_root(green);
    let record = root
        .descendants()
        .find(|node| node.kind() == SyntaxKind::ProjectionRecordTail)
        .expect("record projection tail");
    let spreads = record
        .children()
        .filter(|node| node.kind() == SyntaxKind::ProjectionRecordSpreadItem)
        .collect::<Vec<_>>();
    assert_eq!(spreads.len(), 1);
    assert_eq!(
        spreads[0]
            .descendants_with_tokens()
            .filter_map(|element| element.into_token())
            .map(|token| token.kind())
            .collect::<Vec<_>>(),
        [
            SyntaxKind::Whitespace,
            SyntaxKind::DotDot,
            SyntaxKind::Identifier,
        ]
    );
    assert_eq!(
        spreads[0]
            .children()
            .filter(|node| node.kind() == SyntaxKind::OperatorChain)
            .count(),
        1
    );
    assert!(!record.descendants_with_tokens().any(|node| matches!(
        node.kind(),
        SyntaxKind::Missing | SyntaxKind::Error | SyntaxKind::Invalid
    )));
}

#[test]
fn record_projection_spread_recovers_its_mandatory_rhs() {
    for (source, boundary_at) in [("a.{..}", 5), ("a.{.., next}", 5)] {
        let (green, exit) = run(source);
        assert_eq!(green.to_string(), source, "{source:?}");
        assert!(matches!(exit, Some(Err(Either::Right(_)))), "{source:?}");

        let root = SyntaxNode::new_root(green);
        let record = root
            .descendants()
            .find(|node| node.kind() == SyntaxKind::ProjectionRecordTail)
            .expect("record projection tail");
        let spread = record
            .children()
            .find(|node| node.kind() == SyntaxKind::ProjectionRecordSpreadItem)
            .expect("record spread item");
        assert_eq!(
            spread
                .children_with_tokens()
                .map(|element| element.kind())
                .collect::<Vec<_>>(),
            [SyntaxKind::DotDot, SyntaxKind::Missing],
            "{source:?}"
        );
        assert_eq!(
            spread.children().last().map(|node| node.kind()),
            Some(SyntaxKind::Missing),
            "{source:?}"
        );
        assert_eq!(
            spread
                .children()
                .find(|node| node.kind() == SyntaxKind::Missing)
                .expect("required spread RHS Missing")
                .text_range(),
            rowan::TextRange::empty(boundary_at.into()),
            "{source:?}"
        );
        assert_eq!(
            spread
                .children()
                .filter(|node| node.kind() == SyntaxKind::Missing)
                .count(),
            1,
            "{source:?}"
        );
        assert_eq!(spread.parent().as_ref(), Some(&record), "{source:?}");
        assert!(
            !record
                .descendants_with_tokens()
                .any(|node| matches!(node.kind(), SyntaxKind::Error | SyntaxKind::Invalid)),
            "{source:?}"
        );
    }
}

#[test]
fn record_projection_spread_emits_ordinary_eof_leading_before_rhs_missing() {
    let source = "a.{.. ";
    let (green, exit) = run(source);
    assert_eq!(green.to_string(), source);
    assert!(matches!(exit, Some(Err(Either::Right(_)))));

    let root = SyntaxNode::new_root(green);
    let spread = root
        .descendants()
        .find(|node| node.kind() == SyntaxKind::ProjectionRecordSpreadItem)
        .expect("record spread item");
    let direct = spread.children_with_tokens().collect::<Vec<_>>();
    assert_eq!(
        direct
            .iter()
            .map(|element| element.kind())
            .collect::<Vec<_>>(),
        [
            SyntaxKind::DotDot,
            SyntaxKind::Whitespace,
            SyntaxKind::Missing
        ]
    );
    assert_eq!(
        direct[1].text_range(),
        rowan::TextRange::new(5.into(), 6.into())
    );
    assert_eq!(direct[2].text_range(), rowan::TextRange::empty(6.into()));
    assert_eq!(direct[1].parent().as_ref(), Some(&spread));
    assert_eq!(direct[2].parent().as_ref(), Some(&spread));
}

#[test]
fn record_projection_spread_emits_initial_malformed_leading_before_rhs_error() {
    let source = "a.{.. @}";
    let (green, exit) = run(source);
    assert_eq!(green.to_string(), source);
    assert!(matches!(exit, Some(Err(Either::Right(_)))));

    let root = SyntaxNode::new_root(green);
    let spread = root
        .descendants()
        .find(|node| node.kind() == SyntaxKind::ProjectionRecordSpreadItem)
        .expect("record spread item");
    let direct = spread.children_with_tokens().collect::<Vec<_>>();
    assert_eq!(
        direct
            .iter()
            .map(|element| element.kind())
            .collect::<Vec<_>>(),
        [
            SyntaxKind::DotDot,
            SyntaxKind::Whitespace,
            SyntaxKind::Error
        ]
    );
    assert_eq!(
        direct[1].text_range(),
        rowan::TextRange::new(5.into(), 6.into())
    );
    assert_eq!(
        direct[2].text_range(),
        rowan::TextRange::new(6.into(), 7.into())
    );
    assert_eq!(direct[1].parent().as_ref(), Some(&spread));
    assert_eq!(direct[2].parent().as_ref(), Some(&spread));
}

#[test]
fn record_projection_spread_raw_error_group_includes_internal_trivia_before_retry() {
    let source = "a.{..@ @ rest}";
    let (green, exit) = run(source);
    assert_eq!(green.to_string(), source);
    assert!(matches!(exit, Some(Err(Either::Right(_)))));

    let root = SyntaxNode::new_root(green);
    let spread = root
        .descendants()
        .find(|node| node.kind() == SyntaxKind::ProjectionRecordSpreadItem)
        .expect("record spread item");
    let direct = spread.children_with_tokens().collect::<Vec<_>>();
    assert_eq!(
        direct
            .iter()
            .map(|element| element.kind())
            .collect::<Vec<_>>(),
        [
            SyntaxKind::DotDot,
            SyntaxKind::Error,
            SyntaxKind::Error,
            SyntaxKind::Error,
            SyntaxKind::OperatorChain,
        ]
    );
    assert_eq!(
        direct[1].text_range(),
        rowan::TextRange::new(5.into(), 6.into())
    );
    assert_eq!(
        direct[2].text_range(),
        rowan::TextRange::new(6.into(), 7.into())
    );
    assert_eq!(
        direct[3].text_range(),
        rowan::TextRange::new(7.into(), 8.into())
    );
    assert_eq!(direct[2].parent().as_ref(), Some(&spread));
    let rhs = direct[4].as_node().expect("retried spread RHS");
    assert_eq!(rhs.text_range(), rowan::TextRange::new(8.into(), 13.into()));
    assert!(!rhs.text_range().contains_range(direct[2].text_range()));
    assert!(!rhs.text_range().contains_range(direct[3].text_range()));
}

#[test]
fn record_projection_spread_rejected_marker_orders_rhs_missing_before_parent_recovery() {
    let source = "a.{.. ..rest}";
    let (green, exit) = run(source);
    assert_eq!(green.to_string(), source);
    assert!(matches!(exit, Some(Err(Either::Right(_)))));

    let root = SyntaxNode::new_root(green);
    let record = root
        .descendants()
        .find(|node| node.kind() == SyntaxKind::ProjectionRecordTail)
        .expect("record projection tail");
    let spreads = record
        .children()
        .filter(|node| node.kind() == SyntaxKind::ProjectionRecordSpreadItem)
        .collect::<Vec<_>>();
    assert_eq!(spreads.len(), 2);
    let first_direct = spreads[0].children_with_tokens().collect::<Vec<_>>();
    assert_eq!(
        first_direct
            .iter()
            .map(|element| element.kind())
            .collect::<Vec<_>>(),
        [SyntaxKind::DotDot, SyntaxKind::Missing]
    );
    let first_missing = first_direct[1].as_node().expect("first spread RHS Missing");
    assert_eq!(
        first_missing.text_range(),
        rowan::TextRange::empty(5.into())
    );
    let parent_missing = record
        .children()
        .filter(|node| node.kind() == SyntaxKind::Missing)
        .find(|node| node.text_range() == first_missing.text_range())
        .expect("parent separator recovery at rejected marker");
    assert_eq!(parent_missing.parent().as_ref(), Some(&record));
    let preorder = record
        .descendants()
        .filter(|node| node.kind() == SyntaxKind::Missing)
        .collect::<Vec<_>>();
    let first = preorder
        .iter()
        .position(|node| node.parent().as_ref() == Some(&spreads[0]))
        .expect("first spread RHS Missing in preorder");
    let later = preorder
        .iter()
        .position(|node| node.parent().as_ref() == Some(&record))
        .expect("parent recovery in preorder");
    assert!(first < later);
}

#[test]
fn record_projection_spread_hands_abstract_boundary_out_after_rhs_missing() {
    let fence = crate::lexical::yumark::FenceBoundary {
        opener: crate::lexical::yumark::FenceOpener {
            line: 0,
            marker: 0..3,
            marker_width: 3,
        },
        prefix_policy: crate::lexical::yumark::FencePrefixPolicy::ActivePrefixQuote {
            depth: 2,
            base: 0,
        },
        close_column: 0,
    };
    let source = "> > a.{.. \n> > ```\nouter";
    let (green, exit, remainder) = run_normalized(
        source,
        &OperatorTable::empty(),
        0,
        LineEntry::PhysicalStart,
        Some(&fence),
    );
    assert_eq!(green.to_string(), "> > a.{..");
    let Some(NormalizedExit::Complete(Err(Either::Left(boundary)), LineEntry::PhysicalStart)) =
        exit
    else {
        panic!("record spread must preserve the abstract boundary")
    };
    assert!(boundary.payload_view().is_boundary());
    assert!(boundary.leading_view().has_ordinary_newline());
    assert_eq!(remainder, "> > ```\nouter");

    let root = SyntaxNode::new_root(green);
    let spread = root
        .descendants()
        .find(|node| node.kind() == SyntaxKind::ProjectionRecordSpreadItem)
        .expect("record spread item");
    let direct = spread.children_with_tokens().collect::<Vec<_>>();
    assert_eq!(
        direct
            .iter()
            .map(|element| element.kind())
            .collect::<Vec<_>>(),
        [SyntaxKind::DotDot, SyntaxKind::Missing]
    );
    assert_eq!(direct[1].text_range(), rowan::TextRange::empty(9.into()));
    assert_eq!(direct[1].parent().as_ref(), Some(&spread));
}

#[test]
fn record_projection_spread_retains_a_raw_terminal_rhs_error_at_close() {
    let source = "a.{..@}";
    let (green, exit) = run(source);
    assert_eq!(green.to_string(), source);
    assert!(matches!(exit, Some(Err(Either::Right(_)))));

    let root = SyntaxNode::new_root(green);
    let spread = root
        .descendants()
        .find(|node| node.kind() == SyntaxKind::ProjectionRecordSpreadItem)
        .expect("record spread item");
    assert_eq!(
        spread
            .children_with_tokens()
            .map(|element| element.kind())
            .collect::<Vec<_>>(),
        [SyntaxKind::DotDot, SyntaxKind::Error]
    );
    assert_eq!(
        spread
            .children_with_tokens()
            .find(|element| element.kind() == SyntaxKind::Error)
            .expect("raw terminal RHS Error")
            .text_range(),
        rowan::TextRange::new(5.into(), 6.into())
    );
    assert!(
        !spread
            .children()
            .any(|node| node.kind() == SyntaxKind::Missing)
    );
}

#[test]
fn record_projection_spread_retries_one_raw_error_rhs_run_with_nested_leading() {
    let source = "a.{..@ rest}";
    let (green, exit) = run(source);
    assert_eq!(green.to_string(), source);
    assert!(matches!(exit, Some(Err(Either::Right(_)))));

    let root = SyntaxNode::new_root(green);
    let spread = root
        .descendants()
        .find(|node| node.kind() == SyntaxKind::ProjectionRecordSpreadItem)
        .expect("record spread item");
    assert_eq!(
        spread
            .children_with_tokens()
            .map(|element| element.kind())
            .collect::<Vec<_>>(),
        [
            SyntaxKind::DotDot,
            SyntaxKind::Error,
            SyntaxKind::OperatorChain,
        ]
    );
    let error = spread
        .children_with_tokens()
        .find(|element| element.kind() == SyntaxKind::Error)
        .expect("spread RHS Error");
    assert_eq!(
        error.text_range(),
        rowan::TextRange::new(5.into(), 6.into())
    );
    let rhs = spread
        .children()
        .find(|node| node.kind() == SyntaxKind::OperatorChain)
        .expect("retried spread RHS");
    let leading = rhs
        .descendants_with_tokens()
        .find(|element| element.kind() == SyntaxKind::Whitespace)
        .expect("retried RHS leading");
    assert_eq!(
        leading.text_range(),
        rowan::TextRange::new(6.into(), 7.into())
    );
    assert!(!error.text_range().contains_range(leading.text_range()));
    assert!(rhs.text_range().contains_range(leading.text_range()));
    assert!(
        !spread
            .children()
            .any(|node| node.kind() == SyntaxKind::Missing)
    );
}

#[test]
fn record_projection_spread_is_a_delimited_item_boundary() {
    for (source, expected_spreads, expected_missing, expected_error) in [
        ("a.{x ..rest}", 1, 1, 0),
        ("a.{..x ..rest}", 2, 1, 0),
        ("a.{@ ..rest}", 1, 0, 1),
    ] {
        let (green, exit) = run(source);
        assert_eq!(green.to_string(), source, "{source:?}");
        assert!(matches!(exit, Some(Err(Either::Right(_)))), "{source:?}");

        let root = SyntaxNode::new_root(green);
        let record = root
            .descendants()
            .find(|node| node.kind() == SyntaxKind::ProjectionRecordTail)
            .expect("record projection tail");
        assert_eq!(
            record
                .children()
                .filter(|node| node.kind() == SyntaxKind::ProjectionRecordSpreadItem)
                .count(),
            expected_spreads,
            "{source:?}"
        );
        assert_eq!(
            record
                .descendants()
                .filter(|node| node.kind() == SyntaxKind::Missing)
                .count(),
            expected_missing,
            "{source:?}"
        );
        assert_eq!(
            crate::tests::recovery_output::recovery_groups(&record)
                .into_iter()
                .count(),
            expected_error,
            "{source:?}"
        );
    }
}

#[test]
fn record_projection_spread_yields_to_an_accepted_dynamic_led() {
    let source = "a.{left .. right}";
    let operators = OperatorTable::from_declarations([OperatorDeclaration::new(
        "..",
        OperatorFixities::new().with_infix(BindingPower::scalar(40), BindingPower::new(40, [1])),
    )])
    .expect("a direct parser operator table");
    let (green, exit) = run_with(source, &operators);
    assert_eq!(green.to_string(), source);
    assert!(matches!(exit, Some(Err(Either::Right(_)))));

    let root = SyntaxNode::new_root(green);
    let record = root
        .descendants()
        .find(|node| node.kind() == SyntaxKind::ProjectionRecordTail)
        .expect("record projection tail");
    assert_eq!(
        record
            .children()
            .filter(|node| node.kind() == SyntaxKind::OperatorChain)
            .count(),
        1
    );
    assert!(!record.descendants_with_tokens().any(|node| matches!(
        node.kind(),
        SyntaxKind::ProjectionRecordSpreadItem
            | SyntaxKind::Missing
            | SyntaxKind::Error
            | SyntaxKind::Invalid
    )));
}

#[test]
fn record_projection_spread_rhs_keeps_a_rejected_marker_for_the_owner() {
    for (source, expected_missing, expected_error) in
        [("a.{.. ..rest}", 2, 0), ("a.{..@ ..rest}", 1, 1)]
    {
        let (green, exit) = run(source);
        assert_eq!(green.to_string(), source, "{source:?}");
        assert!(matches!(exit, Some(Err(Either::Right(_)))), "{source:?}");

        let root = SyntaxNode::new_root(green);
        let record = root
            .descendants()
            .find(|node| node.kind() == SyntaxKind::ProjectionRecordTail)
            .expect("record projection tail");
        assert_eq!(
            record
                .children()
                .filter(|node| node.kind() == SyntaxKind::ProjectionRecordSpreadItem)
                .count(),
            2,
            "{source:?}"
        );
        assert_eq!(
            record
                .descendants()
                .filter(|node| node.kind() == SyntaxKind::Missing)
                .count(),
            expected_missing,
            "{source:?}"
        );
        assert_eq!(
            crate::tests::recovery_output::recovery_groups(&record)
                .into_iter()
                .count(),
            expected_error,
            "{source:?}"
        );
    }
}

#[test]
fn record_projection_spread_does_not_split_longer_operator_spellings() {
    let operators = OperatorTable::from_declarations([
        OperatorDeclaration::new(
            "...",
            OperatorFixities::new().with_prefix(BindingPower::scalar(70)),
        ),
        OperatorDeclaration::new(
            "..+",
            OperatorFixities::new().with_prefix(BindingPower::scalar(70)),
        ),
    ])
    .expect("a direct parser operator table");
    for source in ["a.{...rest}", "a.{..+rest}"] {
        let (green, exit) = run_with(source, &operators);
        assert_eq!(green.to_string(), source, "{source:?}");
        assert!(matches!(exit, Some(Err(Either::Right(_)))), "{source:?}");
        assert!(
            !SyntaxNode::new_root(green)
                .descendants()
                .any(|node| node.kind() == SyntaxKind::ProjectionRecordSpreadItem),
            "{source:?}"
        );
    }
}

#[test]
fn dot_projections_precede_field_dispatch_and_own_their_closes() {
    let source = "a.(x,y).{left,right}";
    let (green, exit) = run(source);
    assert_eq!(green.to_string(), source);
    assert!(matches!(exit, Some(Err(Either::Right(_)))));

    let root = SyntaxNode::new_root(green);
    let outer = root
        .children()
        .find(|node| node.kind() == SyntaxKind::OperatorChain)
        .expect("outer expression chain");
    assert_eq!(
        outer.children().map(|node| node.kind()).collect::<Vec<_>>(),
        [
            SyntaxKind::IdentifierExpression,
            SyntaxKind::ProjectionTupleTail,
            SyntaxKind::ProjectionRecordTail,
        ]
    );
    for (kind, close, expected_items) in [
        (SyntaxKind::ProjectionTupleTail, SyntaxKind::RParen, 2),
        (SyntaxKind::ProjectionRecordTail, SyntaxKind::RBrace, 2),
    ] {
        let projection = outer
            .children()
            .find(|node| node.kind() == kind)
            .expect("projection tail");
        assert_eq!(
            projection
                .children()
                .filter(|node| node.kind() == SyntaxKind::OperatorChain)
                .count(),
            expected_items
        );
        let close = projection
            .children_with_tokens()
            .filter_map(|element| element.into_token())
            .find(|token| token.kind() == close)
            .expect("projection close");
        assert_eq!(close.parent().expect("close owner").kind(), kind);
    }
    assert!(!root.descendants_with_tokens().any(|node| matches!(
        node.kind(),
        SyntaxKind::Missing | SyntaxKind::Error | SyntaxKind::Invalid
    )));
}

#[test]
fn index_item_accepts_ml_argument_without_separator_recovery() {
    let (green, exit) = run("x[a b]");
    assert_eq!(green.to_string(), "x[a b]");
    assert!(matches!(exit, Some(Err(Either::Right(_)))));

    let root = SyntaxNode::new_root(green);
    let outer_chain = root
        .children()
        .find(|node| node.kind() == SyntaxKind::OperatorChain)
        .expect("outer expression chain");
    let indexes = outer_chain
        .children()
        .filter(|node| node.kind() == SyntaxKind::IndexTail)
        .collect::<Vec<_>>();
    assert_eq!(indexes.len(), 1);
    let items = indexes[0]
        .children()
        .filter(|node| node.kind() == SyntaxKind::IndexItem)
        .collect::<Vec<_>>();
    assert_eq!(items.len(), 1);
    let item_chain = items[0]
        .children()
        .find(|node| node.kind() == SyntaxKind::OperatorChain)
        .expect("the index item owns its expression chain");
    let ml_arguments = item_chain
        .children()
        .filter(|node| node.kind() == SyntaxKind::MlArgument)
        .collect::<Vec<_>>();
    assert_eq!(ml_arguments.len(), 1);
    assert_ml_children(
        &item_chain,
        &[
            (SyntaxKind::IdentifierExpression, 2..3),
            (SyntaxKind::Whitespace, 3..4),
            (SyntaxKind::MlArgument, 4..5),
        ],
    );
    assert_ml_children(&ml_arguments[0], &[(SyntaxKind::OperatorChain, 4..5)]);
    let argument_chain = ml_arguments[0]
        .children()
        .find(|node| node.kind() == SyntaxKind::OperatorChain)
        .expect("the ML argument owns its expression chain");
    assert_eq!(
        argument_chain
            .descendants_with_tokens()
            .filter_map(|element| element.into_token())
            .map(|token| token.text().to_owned())
            .collect::<Vec<_>>(),
        ["b"]
    );
    assert_eq!(
        root.descendants_with_tokens()
            .filter_map(|element| element.into_token())
            .map(|token| token.kind())
            .collect::<Vec<_>>(),
        [
            SyntaxKind::Identifier,
            SyntaxKind::LBracket,
            SyntaxKind::Identifier,
            SyntaxKind::Whitespace,
            SyntaxKind::Identifier,
            SyntaxKind::RBracket,
        ]
    );
    let rbracket = root
        .descendants_with_tokens()
        .filter_map(|element| element.into_token())
        .find(|token| token.kind() == SyntaxKind::RBracket)
        .expect("index close");
    assert_eq!(
        rbracket.parent().expect("index close owner").kind(),
        SyntaxKind::IndexTail
    );
    assert!(!root.descendants_with_tokens().any(|node| matches!(
        node.kind(),
        SyntaxKind::Missing | SyntaxKind::Error | SyntaxKind::Invalid
    )));
}

#[test]
fn index_item_multiple_ml_arguments_stay_siblings() {
    let (green, exit) = run("x[a b c]");
    assert_eq!(green.to_string(), "x[a b c]");
    assert!(matches!(exit, Some(Err(Either::Right(_)))));

    let root = SyntaxNode::new_root(green);
    let outer_chain = root
        .children()
        .find(|node| node.kind() == SyntaxKind::OperatorChain)
        .expect("outer expression chain");
    let index = outer_chain
        .children()
        .find(|node| node.kind() == SyntaxKind::IndexTail)
        .expect("outer index tail");
    let item_chain = index
        .children()
        .find(|node| node.kind() == SyntaxKind::IndexItem)
        .and_then(|item| {
            item.children()
                .find(|node| node.kind() == SyntaxKind::OperatorChain)
        })
        .expect("the index item owns its expression chain");
    let arguments = item_chain
        .children()
        .filter(|node| node.kind() == SyntaxKind::MlArgument)
        .collect::<Vec<_>>();
    assert_eq!(arguments.len(), 2);
    assert_ml_children(
        &item_chain,
        &[
            (SyntaxKind::IdentifierExpression, 2..3),
            (SyntaxKind::Whitespace, 3..4),
            (SyntaxKind::MlArgument, 4..5),
            (SyntaxKind::Whitespace, 5..6),
            (SyntaxKind::MlArgument, 6..7),
        ],
    );
    for argument in arguments {
        assert!(
            !argument
                .descendants()
                .skip(1)
                .any(|node| node.kind() == SyntaxKind::MlArgument)
        );
    }
}

#[test]
fn index_item_ml_child_keeps_its_continuation_after_call() {
    let (green, exit) = run("x[a b(c) d]");
    assert_eq!(green.to_string(), "x[a b(c) d]");
    assert!(matches!(exit, Some(Err(Either::Right(_)))));

    let root = SyntaxNode::new_root(green);
    let outer_chain = root
        .children()
        .find(|node| node.kind() == SyntaxKind::OperatorChain)
        .expect("outer expression chain");
    let index = outer_chain
        .children()
        .find(|node| node.kind() == SyntaxKind::IndexTail)
        .expect("outer index tail");
    let item_chain = index
        .children()
        .find(|node| node.kind() == SyntaxKind::IndexItem)
        .and_then(|item| {
            item.children()
                .find(|node| node.kind() == SyntaxKind::OperatorChain)
        })
        .expect("the index item owns its expression chain");
    let arguments = item_chain
        .children()
        .filter(|node| node.kind() == SyntaxKind::MlArgument)
        .collect::<Vec<_>>();
    assert_eq!(arguments.len(), 2);
    assert_ml_children(
        &item_chain,
        &[
            (SyntaxKind::IdentifierExpression, 2..3),
            (SyntaxKind::Whitespace, 3..4),
            (SyntaxKind::MlArgument, 4..8),
            (SyntaxKind::Whitespace, 8..9),
            (SyntaxKind::MlArgument, 9..10),
        ],
    );
    for (kind, range, owner) in [
        (SyntaxKind::RParen, 7..8, SyntaxKind::CallTail),
        (SyntaxKind::RBracket, 10..11, SyntaxKind::IndexTail),
    ] {
        let token = root
            .descendants_with_tokens()
            .find(|element| element.kind() == kind)
            .unwrap()
            .into_token()
            .unwrap();
        assert_eq!(
            usize::from(token.text_range().start())..usize::from(token.text_range().end()),
            range
        );
        assert_eq!(token.parent().unwrap().kind(), owner);
    }
    assert!(
        arguments[0]
            .descendants()
            .any(|node| node.kind() == SyntaxKind::CallTail)
    );
    for argument in arguments {
        assert!(
            !argument
                .descendants()
                .skip(1)
                .any(|node| node.kind() == SyntaxKind::MlArgument)
        );
    }
}

#[test]
fn index_item_nested_call_keeps_close_owner_control() {
    let (green, exit) = run("x[a(b)]");
    assert_eq!(green.to_string(), "x[a(b)]");
    assert!(matches!(exit, Some(Err(Either::Right(_)))));

    let root = SyntaxNode::new_root(green);
    let outer_chain = root
        .children()
        .find(|node| node.kind() == SyntaxKind::OperatorChain)
        .expect("outer expression chain");
    let index = outer_chain
        .children()
        .find(|node| node.kind() == SyntaxKind::IndexTail)
        .expect("outer index tail");
    let items = index
        .children()
        .filter(|node| node.kind() == SyntaxKind::IndexItem)
        .collect::<Vec<_>>();
    assert_eq!(items.len(), 1);
    let item_chain = items[0]
        .children()
        .find(|node| node.kind() == SyntaxKind::OperatorChain)
        .expect("the index item owns its expression chain");
    let call = item_chain
        .children()
        .find(|node| node.kind() == SyntaxKind::CallTail)
        .expect("the index expression owns its nested call tail");
    assert_eq!(
        call.children()
            .filter(|node| node.kind() == SyntaxKind::OperatorChain)
            .count(),
        1
    );
    assert_eq!(
        root.descendants_with_tokens()
            .filter_map(|element| element.into_token())
            .map(|token| token.kind())
            .collect::<Vec<_>>(),
        [
            SyntaxKind::Identifier,
            SyntaxKind::LBracket,
            SyntaxKind::Identifier,
            SyntaxKind::LParen,
            SyntaxKind::Identifier,
            SyntaxKind::RParen,
            SyntaxKind::RBracket,
        ]
    );
    let rparen = root
        .descendants_with_tokens()
        .filter_map(|element| element.into_token())
        .find(|token| token.kind() == SyntaxKind::RParen)
        .expect("call close");
    assert_eq!(
        rparen.parent().expect("call close owner").kind(),
        SyntaxKind::CallTail
    );
    let rbracket = root
        .descendants_with_tokens()
        .filter_map(|element| element.into_token())
        .find(|token| token.kind() == SyntaxKind::RBracket)
        .expect("index close");
    assert_eq!(
        rbracket.parent().expect("index close owner").kind(),
        SyntaxKind::IndexTail
    );
    assert!(!root.descendants_with_tokens().any(|node| matches!(
        node.kind(),
        SyntaxKind::Missing | SyntaxKind::Error | SyntaxKind::Invalid
    )));
}
