use crate::tests::support::*;
use crate::{
    ambient_claim::AmbientClaimView, handoff::MlMode, sequence::SequenceOwner,
    statement::StatementLineHandoff, structural_diagnostic::StructuralKind,
};

fn parse<'s>(
    source: &'s str,
    stops: Stops,
    origin: usize,
    fence: Option<&FenceBoundary>,
) -> (GreenNode, NormalizedExit, &'s str) {
    let operators = OperatorTable::empty();
    let mut input = source;
    let mut recover = Recover::new_for_test(&operators);
    let mut output = GreenNodeBuilder::new();
    output.start_node(SyntaxKind::Root.into());
    let exit = expr_normalized(
        crate::cursor::SyntaxIn::new(&mut input, &mut recover, &mut output),
        None,
        0,
        stops,
        MlMode::All,
        StatementLineHandoff::OrdinaryLayout,
        origin,
        LineEntry::InLine,
        fence,
        Some(AmbientClaimView::root_statement(0)).into(),
        None,
    )
    .unwrap();
    output.finish_node();
    (
        finish_with_discarded_recoveries(output, recover),
        exit,
        input,
    )
}

fn parse_with_sequence(
    source: &str,
    sequence: Option<SequenceOwner>,
) -> (GreenNode, NormalizedExit) {
    let operators = OperatorTable::empty();
    let mut input = source;
    let mut recover = Recover::new_for_test(&operators);
    let mut output = GreenNodeBuilder::new();
    output.start_node(SyntaxKind::Root.into());
    let exit = expr_normalized(
        crate::cursor::SyntaxIn::new(&mut input, &mut recover, &mut output),
        None,
        0,
        0,
        MlMode::All,
        StatementLineHandoff::OrdinaryLayout,
        0,
        LineEntry::InLine,
        None,
        Some(AmbientClaimView::root_statement(0)).into(),
        sequence,
    )
    .unwrap();
    output.finish_node();
    (finish_with_discarded_recoveries(output, recover), exit)
}

fn structural_fact(kind: StructuralKind, range: std::ops::Range<usize>) -> StructuralFact {
    (kind, range)
}

#[test]
fn inline_slots_have_exact_structural_facts() {
    for (source, kind, range) in [
        ("f:", StructuralKind::Missing, 2..2),
        ("f:   ", StructuralKind::Missing, 5..5),
        ("f: , x", StructuralKind::Missing, 2..2),
        ("f: x,", StructuralKind::Missing, 5..5),
        ("f: @ @ x", StructuralKind::ErrorGroup, 3..6),
        ("f: => x", StructuralKind::ErrorGroup, 3..5),
        ("f: @ ]", StructuralKind::ErrorGroup, 3..4),
        ("f with", StructuralKind::Missing, 6..6),
        ("f with x", StructuralKind::Missing, 6..6),
        ("f with :: x", StructuralKind::Missing, 6..6),
        ("f with: ", StructuralKind::Missing, 8..8),
        ("f with:\nnext", StructuralKind::Missing, 7..7),
        ("f with: ;", StructuralKind::Missing, 7..7),
        ("f with ;", StructuralKind::Missing, 6..6),
        ("f with: @ @ x", StructuralKind::ErrorGroup, 8..11),
    ] {
        let (green, _, _) = parse(source, 0, 0, None);
        let facts = structural_facts(&green);
        assert_eq!(facts, [structural_fact(kind, range.clone())], "{source:?}");
        if kind == StructuralKind::ErrorGroup {
            let error = crate::tests::recovery_output::recovery_groups(&SyntaxNode::new_root(
                green.clone(),
            ))
            .into_iter()
            .next()
            .expect("CST Error group");
            assert_eq!(error.text().to_string(), source[range]);
        }
    }
}

#[test]
fn with_retry_admits_canonical_statements_and_literals() {
    for body in [
        "x",
        "pub x = y",
        "use x",
        "struct X {}",
        "pub enum E;",
        "pub error E;",
        "pub role R;",
        "pub impl T;",
        "pub cast(x): T;",
        "pub act A;",
        "\"text\"",
        "\"\"\"raw\"\"\"",
        "~\"raw\"",
    ] {
        for prefix in ["f with: ", "f with: @ @ "] {
            let source = format!("{prefix}{body}");
            let (green, _, _) = parse(&source, 0, 0, None);
            assert_eq!(green.to_string(), source);
            let expected = if prefix.contains('@') {
                vec![structural_fact(StructuralKind::ErrorGroup, 8..11)]
            } else {
                vec![]
            };
            assert_eq!(structural_facts(&green), expected, "{source:?}");
        }
    }
}

#[test]
fn inline_boundaries_preserve_the_whole_pending_item() {
    use crate::lexical::stops::STOP_COMMA;
    for (source, stops, emitted, pending, start, kind, range) in [
        (
            "f: , x",
            STOP_COMMA,
            "f:",
            TokenKind::Comma,
            2,
            StructuralKind::Missing,
            2..2,
        ),
        (
            "f: @ ]",
            0,
            "f: @",
            TokenKind::RBracket,
            4,
            StructuralKind::ErrorGroup,
            3..4,
        ),
        (
            "f: @ , x",
            STOP_COMMA,
            "f: @",
            TokenKind::Comma,
            4,
            StructuralKind::ErrorGroup,
            3..4,
        ),
        (
            "f: -> x",
            STOP_ARROW,
            "f:",
            TokenKind::Arrow,
            2,
            StructuralKind::Missing,
            2..2,
        ),
        (
            "f with: @ ]",
            0,
            "f with: @",
            TokenKind::RBracket,
            9,
            StructuralKind::ErrorGroup,
            8..9,
        ),
        (
            "f with :: x",
            0,
            "f with",
            TokenKind::PathSeparator,
            6,
            StructuralKind::Missing,
            6..6,
        ),
    ] {
        let (green, exit, remainder) = parse(source, stops, 0, None);
        assert_eq!(
            structural_facts(&green),
            [structural_fact(kind, range)],
            "{source:?}"
        );
        assert_eq!(green.to_string(), emitted);
        let NormalizedExit::Complete(Err(Either::Left(item)), _) = exit else {
            panic!("pending boundary")
        };
        assert_eq!(token_kind(&item), Some(pending));
        assert_eq!(
            item.extent(source.len() - remainder.len())
                .recovery_range()
                .start,
            start
        );
    }
}

#[test]
fn inline_utf8_crlf_and_quoted_fences_keep_physical_coordinates() {
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
    for (source, kind, range, emitted) in [
        ("f:\r\n> > ```\nouter", StructuralKind::Missing, 2..2, "f:"),
        (
            "f: 💥\r\n> > ```\nouter",
            StructuralKind::ErrorGroup,
            3..7,
            "f: 💥",
        ),
        (
            "f with:\r\n> > ```\nouter",
            StructuralKind::Missing,
            7..7,
            "f with:",
        ),
        (
            "f with: 💥\r\n> > ```\nouter",
            StructuralKind::ErrorGroup,
            8..12,
            "f with: 💥",
        ),
    ] {
        let (green, exit, remainder) = parse(source, 0, 100, Some(&fence));
        assert_eq!(structural_facts(&green), [structural_fact(kind, range)]);
        assert_eq!(green.to_string(), emitted);
        assert_eq!(remainder, "> > ```\nouter");
        assert!(matches!(
            exit,
            NormalizedExit::Complete(Err(Either::Left(_)), LineEntry::PhysicalStart)
        ));
    }
    let source = "f with @\r\n> > ```\nouter";
    let (green, exit, remainder) = parse(source, 0, 100, Some(&fence));
    assert_eq!(
        structural_facts(&green),
        [
            structural_fact(StructuralKind::Missing, 6..6),
            structural_fact(StructuralKind::ErrorGroup, 7..8),
        ]
    );
    assert_eq!(green.to_string(), "f with @");
    assert_eq!(remainder, "> > ```\nouter");
    assert!(matches!(
        exit,
        NormalizedExit::Complete(Err(Either::Left(_)), LineEntry::PhysicalStart)
    ));
}

#[test]
fn inline_nested_slots_keep_distinct_structural_facts() {
    let source = "f with x:";
    let (green, _, _) = parse(source, 0, 0, None);
    assert_eq!(
        structural_facts(&green),
        [
            structural_fact(StructuralKind::Missing, 6..6),
            structural_fact(StructuralKind::Missing, 9..9),
        ]
    );
}

#[test]
fn with_false_prefixed_declaration_candidate_keeps_canonical_fallback() {
    let source = "f with: @ my use";
    let (green, _, _) = parse(source, 0, 0, None);
    assert_eq!(green.to_string(), source);
    assert_eq!(
        structural_facts(&green),
        [structural_fact(StructuralKind::ErrorGroup, 8..9)]
    );
    let root = SyntaxNode::new_root(green);
    assert!(
        !root
            .descendants()
            .any(|node| node.kind() == SyntaxKind::UseDeclaration)
    );
}

#[test]
fn colon_disabled_ml_entry_keeps_seed_and_pending_colon_effect_free() {
    let operators = OperatorTable::empty();
    let mut recover = Recover::new_for_test(&operators);
    let mut input = "f: @";
    let mut output = GreenNodeBuilder::new();
    output.start_node(SyntaxKind::Root.into());
    output.token(SyntaxKind::Identifier.into(), "seed");
    let exit = expr_normalized(
        crate::cursor::SyntaxIn::new(&mut input, &mut recover, &mut output),
        None,
        0,
        0,
        MlMode::None,
        StatementLineHandoff::OrdinaryLayout,
        100,
        LineEntry::InLine,
        None,
        Some(AmbientClaimView::root_statement(0)).into(),
        None,
    )
    .unwrap();
    output.finish_node();
    let green = finish_with_discarded_recoveries(output, recover);
    assert_eq!(green.to_string(), "seedf");
    assert!(structural_facts(&green).is_empty());
    assert_eq!(input, " @");
    let NormalizedExit::Complete(Err(Either::Left(item)), _) = exit else {
        panic!("unread colon")
    };
    assert_eq!(token_kind(&item), Some(TokenKind::Colon));
    assert_eq!(item.extent(102).recovery_range(), 101..102);
}

#[test]
fn line_deferred_with_preserves_the_whole_keyword_without_records() {
    let (green, exit, remainder) = parse("f\nwith x", 0, 0, None);
    assert_eq!(green.to_string(), "f");
    assert!(structural_facts(&green).is_empty());
    assert_eq!(remainder, " x");
    let NormalizedExit::Complete(Err(Either::Left(item)), _) = exit else {
        panic!("pending keyword")
    };
    assert_eq!(item.payload_view().spelling(), Some("with"));
    assert_eq!(item.extent(6).recovery_range(), 1..6);
}

#[test]
fn colon_and_with_cst_slots_are_selected_by_ordered_direct_grammar() {
    colon_local_comma_slots_are_ordered_directly();
    for (source, chains, commas, newlines, missing) in [
        ("f:", 0, 0, 0, true),
        ("f: @ x", 1, 0, 0, false),
        ("f: x,", 1, 1, 0, true),
        ("f: x,, y", 2, 2, 0, true),
        ("f: x, @ y", 2, 1, 0, false),
        ("f: x\ny", 2, 0, 1, false),
        ("f: x\n, y", 2, 1, 1, false),
        ("f: x\n", 1, 0, 1, false),
    ] {
        let (green, _, _) = parse(source, 0, 0, None);
        let root = SyntaxNode::new_root(green);
        let tail = root
            .descendants()
            .find(|node| node.kind() == SyntaxKind::ColonApplicationTail)
            .unwrap();
        let elements = tail.children_with_tokens().collect::<Vec<_>>();
        let colon = elements
            .iter()
            .position(|child| child.kind() == SyntaxKind::Colon)
            .unwrap();
        let first_chain = elements
            .iter()
            .position(|child| child.kind() == SyntaxKind::OperatorChain);
        if let Some(first_chain) = first_chain {
            assert!(colon < first_chain, "{source:?}");
        } else {
            assert!(
                elements[colon + 1..]
                    .iter()
                    .any(|child| child.kind() == SyntaxKind::Missing)
            );
        }
        assert_eq!(
            elements
                .iter()
                .filter(|child| child.kind() == SyntaxKind::OperatorChain)
                .count(),
            chains,
            "{source:?}"
        );
        assert_eq!(
            elements
                .iter()
                .filter(|child| child.kind() == SyntaxKind::Comma)
                .count(),
            commas,
            "{source:?}"
        );
        assert_eq!(
            elements
                .iter()
                .filter(|child| child.kind() == SyntaxKind::Newline)
                .count(),
            newlines,
            "{source:?}"
        );
        assert_eq!(
            elements
                .iter()
                .filter(|child| child.kind() == SyntaxKind::Missing)
                .count(),
            usize::from(missing),
            "{source:?}"
        );
    }

    let (green, exit) = parse_with_sequence("f: x, y", Some(SequenceOwner::RootStatement));
    let root = SyntaxNode::new_root(green);
    let tail = root
        .descendants()
        .find(|node| node.kind() == SyntaxKind::ColonApplicationTail)
        .unwrap();
    assert_eq!(
        tail.children()
            .filter(|child| child.kind() == SyntaxKind::OperatorChain)
            .count(),
        1
    );
    assert!(
        tail.children_with_tokens()
            .all(|child| child.kind() != SyntaxKind::Comma)
    );
    let NormalizedExit::Complete(Err(Either::Left(item)), _) = exit else {
        panic!("outer comma remains pending");
    };
    assert_eq!(token_kind(&item), Some(TokenKind::Comma));

    for (source, expected_body) in [
        ("f with", None),
        ("f with: ]", None),
        ("f with: @ x", Some(SyntaxKind::OperatorChain)),
        ("f with: \"x\"", Some(SyntaxKind::StringLiteral)),
        ("f with: pub x = y", Some(SyntaxKind::BindingStatement)),
    ] {
        let (green, _, _) = parse(source, 0, 0, None);
        let root = SyntaxNode::new_root(green);
        let tail = root
            .descendants()
            .find(|node| node.kind() == SyntaxKind::WithBodyTail)
            .unwrap();
        let elements = tail.children_with_tokens().collect::<Vec<_>>();
        let with = elements
            .iter()
            .position(|child| child.kind() == SyntaxKind::WithKw)
            .unwrap();
        let colon = elements
            .iter()
            .position(|child| child.kind() == SyntaxKind::Colon);
        let missing = elements
            .iter()
            .position(|child| child.kind() == SyntaxKind::Missing);
        match expected_body {
            None => {
                assert!(missing.is_some(), "{source:?}");
                if source == "f with" {
                    assert!(colon.is_none());
                } else {
                    assert!(with < colon.unwrap() && colon.unwrap() < missing.unwrap());
                }
            }
            Some(kind) => {
                let statement = elements
                    .iter()
                    .find_map(|child| child.as_node())
                    .filter(|node| node.kind() == SyntaxKind::Statement)
                    .unwrap();
                assert!(with < colon.unwrap());
                assert!(missing.is_none());
                assert!(statement.descendants().any(|node| node.kind() == kind));
                if source.contains('@') {
                    let error = elements
                        .iter()
                        .position(|child| child.kind() == SyntaxKind::Error)
                        .unwrap();
                    assert!(
                        colon.unwrap() < error
                            && error
                                < elements
                                    .iter()
                                    .position(|child| child.kind() == SyntaxKind::Statement)
                                    .unwrap()
                    );
                }
            }
        }
    }
}

fn colon_local_comma_slots_are_ordered_directly() {
    for (source, recovery, successor) in [
        ("f: x,", SyntaxKind::Missing, None),
        ("f: x,, y", SyntaxKind::Missing, Some(SyntaxKind::Comma)),
        (
            "f: x, @ y",
            SyntaxKind::Error,
            Some(SyntaxKind::OperatorChain),
        ),
    ] {
        let (green, _, _) = parse(source, 0, 0, None);
        let root = SyntaxNode::new_root(green);
        let tail = root
            .descendants()
            .find(|node| node.kind() == SyntaxKind::ColonApplicationTail)
            .unwrap();
        let elements = tail.children_with_tokens().collect::<Vec<_>>();
        let comma = elements
            .iter()
            .position(|child| child.kind() == SyntaxKind::Comma)
            .unwrap();
        let recovery = elements
            .iter()
            .enumerate()
            .skip(comma + 1)
            .find_map(|(index, child)| (child.kind() == recovery).then_some(index))
            .unwrap();
        assert!(comma < recovery, "{source:?}");
        match successor {
            Some(kind) => {
                let successor = elements
                    .iter()
                    .enumerate()
                    .skip(recovery + 1)
                    .find_map(|(index, child)| (child.kind() == kind).then_some(index))
                    .unwrap();
                assert!(recovery < successor, "{source:?}");
                if kind == SyntaxKind::Comma {
                    let retry = elements
                        .iter()
                        .enumerate()
                        .skip(successor + 1)
                        .find_map(|(index, child)| {
                            (child.kind() == SyntaxKind::OperatorChain).then_some(index)
                        })
                        .unwrap();
                    assert!(successor < retry, "{source:?}");
                }
            }
            None => assert_eq!(recovery + 1, elements.len(), "{source:?}"),
        }
    }
}

#[test]
fn colon_and_with_cst_recovery_orders_are_direct_and_terminal() {
    for (source, error_range, terminal) in [("f: @\nx", 3..4, false), ("f: x\n@", 5..6, true)] {
        let (green, _, _) = parse(source, 0, 0, None);
        let root = SyntaxNode::new_root(green);
        let tail = root
            .descendants()
            .find(|node| node.kind() == SyntaxKind::ColonApplicationTail)
            .unwrap();
        let elements = tail.children_with_tokens().collect::<Vec<_>>();
        let error = elements
            .iter()
            .position(|child| child.kind() == SyntaxKind::Error)
            .unwrap();
        let newline = elements
            .iter()
            .position(|child| child.kind() == SyntaxKind::Newline)
            .unwrap();
        assert_eq!(
            elements[error].text_range(),
            rowan::TextRange::new(error_range.start.into(), error_range.end.into())
        );
        if terminal {
            assert!(newline < error);
            assert!(
                elements
                    .iter()
                    .all(|child| child.kind() != SyntaxKind::Missing)
            );
        } else {
            let retry = elements
                .iter()
                .enumerate()
                .skip(newline + 1)
                .find_map(|(index, child)| {
                    (child.kind() == SyntaxKind::OperatorChain).then_some(index)
                })
                .unwrap();
            assert!(error < newline && newline < retry);
        }
    }

    let (green, exit) = parse_with_sequence("f: x\ny", Some(SequenceOwner::RootStatement));
    let root = SyntaxNode::new_root(green);
    let tail = root
        .descendants()
        .find(|node| node.kind() == SyntaxKind::ColonApplicationTail)
        .unwrap();
    assert!(
        tail.children_with_tokens()
            .all(|child| child.kind() != SyntaxKind::Newline)
    );
    assert!(matches!(
        exit,
        NormalizedExit::Complete(Err(Either::Left(_)), _)
    ));

    for (source, expected) in [
        ("f with @ x", Some(SyntaxKind::OperatorChain)),
        ("f with: @", None),
        ("f with: @ \"x\"", Some(SyntaxKind::StringLiteral)),
        ("f with: @ pub x = y", Some(SyntaxKind::BindingStatement)),
    ] {
        let (green, _, _) = parse(source, 0, 0, None);
        let root = SyntaxNode::new_root(green);
        let tail = root
            .descendants()
            .find(|node| node.kind() == SyntaxKind::WithBodyTail)
            .unwrap();
        let elements = tail.children_with_tokens().collect::<Vec<_>>();
        let with = elements
            .iter()
            .position(|child| child.kind() == SyntaxKind::WithKw)
            .unwrap();
        let error = elements
            .iter()
            .position(|child| child.kind() == SyntaxKind::Error)
            .unwrap();
        let missing = elements
            .iter()
            .position(|child| child.kind() == SyntaxKind::Missing);
        assert!(with < error);
        if source == "f with @ x" {
            assert!(missing.unwrap() < error);
        } else {
            assert!(missing.is_none());
        }
        match expected {
            Some(kind) => {
                let statement = elements
                    .iter()
                    .position(|child| child.kind() == SyntaxKind::Statement)
                    .unwrap();
                assert!(error < statement);
                assert!(
                    elements[statement]
                        .as_node()
                        .unwrap()
                        .descendants()
                        .any(|node| node.kind() == kind)
                );
            }
            None => assert!(
                elements
                    .iter()
                    .all(|child| child.kind() != SyntaxKind::Statement)
            ),
        }
    }
}
