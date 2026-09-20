use crate::tests::support::*;
use crate::{ambient_claim::AmbientClaimView, structural_diagnostic::StructuralKind};
use std::ops::Range;

fn parse<'s>(
    source: &'s str,
    origin: usize,
    fence: Option<&FenceBoundary>,
) -> (GreenNode, Vec<StructuralFact>, NormalizedExit, &'s str) {
    let operators = OperatorTable::empty();
    let mut recover = Recover::new_for_test(&operators);
    let mut input = source;
    let mut output = GreenNodeBuilder::new();
    output.start_node(SyntaxKind::Root.into());
    let exit = statement_normalized(
        crate::cursor::SyntaxIn::new(&mut input, &mut recover, &mut output),
        0,
        0,
        origin,
        LineEntry::InLine,
        fence,
        Some(AmbientClaimView::root_statement(0)).into(),
        Some(crate::sequence::SequenceOwner::RootStatement),
    );
    output.finish_node();
    let green = finish_with_discarded_recoveries(output, recover);
    let facts = structural_facts(&green);
    (green, facts, exit, input)
}

fn structural_fact(kind: StructuralKind, range: Range<usize>) -> StructuralFact {
    (kind, range)
}

#[test]
fn braced_slots_have_exact_structural_facts() {
    use StructuralKind::{ErrorGroup, Missing};
    for (source, slots) in [
        ("{,;}", vec![(Missing, 1..1), (Missing, 2..2)]),
        ("{ @ @ α}", vec![(ErrorGroup, 2..5)]),
        ("{@,}", vec![(ErrorGroup, 1..2)]),
        ("{@\n,}", vec![(ErrorGroup, 1..2), (Missing, 3..3)]),
        ("{@\r\n;}", vec![(ErrorGroup, 1..2), (Missing, 4..4)]),
        ("{x\n;}", vec![(Missing, 3..3)]),
        ("{x\r\n,}", vec![(Missing, 4..4)]),
        ("{@}", vec![(ErrorGroup, 1..2)]),
        ("{@  ", vec![(ErrorGroup, 1..2), (Missing, 4..4)]),
        ("{  ", vec![(Missing, 3..3)]),
        ("{use a use b}", vec![(Missing, 6..6)]),
    ] {
        for origin in [0, 137] {
            let (green, facts, _, _) = parse(source, origin, None);
            assert_eq!(green.to_string(), source);
            assert_eq!(facts, slots, "{source:?} at {origin}");
            let (again, repeated_facts, _, _) = parse(source, origin, None);
            assert_eq!(again, green);
            assert_eq!(repeated_facts, facts);
        }
    }
}

#[test]
fn braced_missing_slots_collide_at_the_same_direct_rowan_occurrence_path() {
    let cases = [
        // The comma and semicolon remain in their explicit separator phase.
        (
            "{,;}",
            "required statement",
            1..1,
            vec![
                structural_fact(StructuralKind::Missing, 1..1),
                structural_fact(StructuralKind::Missing, 2..2),
            ],
        ),
        // The second statement is admitted after the missing separator.
        (
            "{use a use b}",
            "separator",
            6..6,
            vec![structural_fact(StructuralKind::Missing, 6..6)],
        ),
        // EOF reaches the local close phase after its horizontal leading.
        (
            "{  ",
            "closing brace",
            3..3,
            vec![structural_fact(StructuralKind::Missing, 3..3)],
        ),
    ];

    let mut paths = Vec::new();
    for (source, role, range, expected) in cases {
        let (green, facts, exit, suffix) = parse(source, 0, None);
        assert_eq!(green.to_string(), source, "{source:?}");
        assert_eq!(facts, expected, "{source:?}");
        assert!(matches!(exit, NormalizedExit::Complete(_, _)), "{source:?}");
        assert_eq!(suffix, "", "{source:?}");

        let root = SyntaxNode::new_root(green.clone());
        let block = root
            .descendants()
            .find(|node| node.kind() == SyntaxKind::BracedStatementBlockExpression)
            .unwrap_or_else(|| panic!("braced block for {source:?}"));
        // Immediate ancestry is shared, but the complete ordered direct
        // children retain the required-item, successor and terminal phases.
        // Select the occurrence by that order, independently of the ledger.
        let children = block.children_with_tokens().collect::<Vec<_>>();
        let (kinds, missing_index) = match source {
            "{,;}" => (
                vec![
                    SyntaxKind::LBrace,
                    SyntaxKind::Missing,
                    SyntaxKind::BlockStatementSeparator,
                    SyntaxKind::Missing,
                    SyntaxKind::BlockStatementSeparator,
                    SyntaxKind::RBrace,
                ],
                1,
            ),
            "{use a use b}" => (
                vec![
                    SyntaxKind::LBrace,
                    SyntaxKind::Statement,
                    SyntaxKind::Missing,
                    SyntaxKind::Statement,
                    SyntaxKind::RBrace,
                ],
                2,
            ),
            "{  " => (
                vec![
                    SyntaxKind::LBrace,
                    SyntaxKind::Whitespace,
                    SyntaxKind::Missing,
                ],
                2,
            ),
            _ => unreachable!(),
        };
        assert_eq!(
            children
                .iter()
                .map(|child| child.kind())
                .collect::<Vec<_>>(),
            kinds,
            "{source:?}",
        );
        for child in &children {
            assert_eq!(child.parent(), Some(block.clone()), "{source:?}");
            assert_eq!(
                child.as_node().is_some(),
                matches!(
                    child.kind(),
                    SyntaxKind::Missing
                        | SyntaxKind::Statement
                        | SyntaxKind::BlockStatementSeparator
                ),
                "{source:?}",
            );
        }
        assert!(
            !block
                .descendants()
                .any(|node| node.kind() == SyntaxKind::Invalid)
        );
        let missing = children[missing_index].as_node().unwrap();
        assert_eq!(missing.kind(), SyntaxKind::Missing);
        assert_eq!(
            missing.text_range(),
            rowan::TextRange::empty(range.start.into())
        );
        assert_eq!(missing.text().to_string(), "", "{role:?}: {source:?}");
        assert!(missing.children_with_tokens().next().is_none());
        if source == "{,;}" {
            for (index, kind, text) in
                [(2, SyntaxKind::Comma, ","), (4, SyntaxKind::Semicolon, ";")]
            {
                let separator = children[index].as_node().unwrap();
                let tokens = separator.children_with_tokens().collect::<Vec<_>>();
                assert_eq!(tokens.len(), 1);
                let token = tokens[0].as_token().unwrap();
                assert_eq!(token.kind(), kind);
                assert_eq!(token.text(), text);
            }
        }
        if source == "{  " {
            let leading = children[1].as_token().unwrap();
            assert_eq!(leading.text(), "  ");
            assert_eq!(
                leading.text_range(),
                rowan::TextRange::new(1.into(), 3.into())
            );
            assert_eq!(missing_index + 1, children.len());
        } else {
            let close = children.last().unwrap().as_token().unwrap();
            assert_eq!(close.kind(), SyntaxKind::RBrace);
            assert_eq!(close.text(), "}");
            assert_eq!(usize::from(close.text_range().end()), source.len());
        }
        assert_eq!(missing.parent(), Some(block.clone()), "{source:?}");
        paths.push(
            missing
                .ancestors()
                .take(2)
                .map(|node| node.kind())
                .collect::<Vec<_>>(),
        );

        if role == "separator" {
            assert_eq!(
                block
                    .children()
                    .filter(|node| node.kind() == SyntaxKind::Statement)
                    .count(),
                2,
                "the second Statement follows its missing separator: {source:?}",
            );
        }

        let (again, repeated_facts, repeated_exit, repeated_suffix) = parse(source, 0, None);
        assert_eq!(again, green, "{source:?}");
        assert_eq!(repeated_facts, facts, "{source:?}");
        assert!(
            matches!(repeated_exit, NormalizedExit::Complete(_, _)),
            "{source:?}"
        );
        assert_eq!(repeated_suffix, suffix, "{source:?}");
    }

    assert_eq!(
        paths,
        vec![
            vec![
                SyntaxKind::Missing,
                SyntaxKind::BracedStatementBlockExpression
            ],
            vec![
                SyntaxKind::Missing,
                SyntaxKind::BracedStatementBlockExpression
            ],
            vec![
                SyntaxKind::Missing,
                SyntaxKind::BracedStatementBlockExpression
            ],
        ],
        "the roles have no CST-visible wrapper between the block and Missing",
    );
}

#[test]
fn protected_nonlocal_closes_keep_horizontal_and_crlf_leading() {
    for prefix in ["{", "{@", "{x;", "{x", "{for x in xs {}"] {
        for leading in ["  ", "\r\n  "] {
            for close in [')', ']'] {
                let source = format!("{prefix}{leading}{close}tail");
                let (green, facts, exit, suffix) = parse(&source, 100, None);
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
                    facts.last(),
                    Some(&structural_fact(
                        StructuralKind::Missing,
                        prefix.len()..prefix.len(),
                    ))
                );
            }
        }
    }
}

#[test]
fn accepted_braced_sequence_controls_have_only_structural_recovery() {
    for source in [
        "{}", "{ }", "{x;}", "{x,}", "{x;  ", "{f x}", "{f: x,y}", "{x\n y}",
    ] {
        let (green, facts, _, _) = parse(source, 0, None);
        assert_eq!(green.to_string(), source);
        if source.ends_with('}') {
            assert!(facts.is_empty(), "{source:?}: {facts:?}");
        } else {
            assert_eq!(facts.len(), 1);
        }
    }
}

#[test]
fn declaration_body_callers_publish_the_braced_child_role() {
    use SyntaxKind::*;

    for prefix in ["mod M ", "role R ", "impl T ", "act A ", "for x in xs "] {
        let source = format!("{prefix}{{ @ }}");
        let (green, facts, exit, suffix) = parse(&source, 0, None);
        assert_eq!(green.to_string(), source);
        assert_eq!(suffix, "");
        let p = prefix.len();
        let root = SyntaxNode::new_root(green.clone());
        let (caller_kind, header) = match prefix {
            "mod M " => (
                ModDeclaration,
                vec![
                    (ModKw, 0..3),
                    (Whitespace, 3..4),
                    (Identifier, 4..5),
                    (Whitespace, 5..6),
                ],
            ),
            "role R " => (
                RoleDeclaration,
                vec![
                    (RoleKw, 0..4),
                    (Whitespace, 4..5),
                    (TypeExpression, 5..6),
                    (Whitespace, 6..7),
                ],
            ),
            "impl T " => (
                ImplDeclaration,
                vec![
                    (ImplKw, 0..4),
                    (Whitespace, 4..5),
                    (TypeExpression, 5..6),
                    (Whitespace, 6..7),
                ],
            ),
            "act A " => (
                ActDeclaration,
                vec![
                    (ActKw, 0..3),
                    (Whitespace, 3..4),
                    (TypeExpression, 4..5),
                    (Whitespace, 5..6),
                ],
            ),
            "for x in xs " => (
                ForStatement,
                vec![
                    (ForKw, 0..3),
                    (Whitespace, 3..4),
                    (Pattern, 4..5),
                    (Whitespace, 5..6),
                    (InKw, 6..8),
                    (Whitespace, 8..9),
                    (ForIterable, 9..11),
                    (Whitespace, 11..12),
                ],
            ),
            _ => unreachable!(),
        };
        let statement = root.children().next().unwrap();
        assert_eq!(root.kind(), Root);
        assert_eq!(root.children_with_tokens().count(), 1);
        assert_eq!(statement.kind(), Statement);
        assert_eq!(statement.children_with_tokens().count(), 1);
        let caller = statement.children().next().unwrap();
        assert_eq!(caller.kind(), caller_kind);
        let children = caller.children_with_tokens().collect::<Vec<_>>();
        assert_eq!(children.len(), header.len() + 1);
        for (child, (kind, range)) in children.iter().zip(&header) {
            assert_eq!(child.parent(), Some(caller.clone()));
            assert_eq!(child.kind(), *kind);
            assert_eq!(
                usize::from(child.text_range().start())..usize::from(child.text_range().end()),
                *range
            );
            assert_eq!(child.to_string(), source[range.clone()]);
            assert_eq!(
                child.as_node().is_some(),
                matches!(kind, TypeExpression | Pattern | ForIterable)
            );
            if let Some(node) = child.as_node() {
                let expected_nodes = match kind {
                    TypeExpression => vec![TypeExpression],
                    Pattern => vec![Pattern, IdentifierPattern],
                    ForIterable => vec![ForIterable, OperatorChain, IdentifierExpression],
                    _ => unreachable!(),
                };
                assert_eq!(
                    node.descendants()
                        .map(|node| node.kind())
                        .collect::<Vec<_>>(),
                    expected_nodes
                );
                let tokens = node
                    .descendants_with_tokens()
                    .filter_map(|child| child.into_token())
                    .collect::<Vec<_>>();
                assert_eq!(tokens.len(), 1);
                assert_eq!(tokens[0].kind(), Identifier);
                assert_eq!(tokens[0].text_range(), node.text_range());
                assert_eq!(tokens[0].text(), &source[range.clone()]);
            }
        }
        let block = children.last().unwrap().as_node().unwrap();
        assert_eq!(
            block
                .ancestors()
                .map(|node| node.kind())
                .collect::<Vec<_>>(),
            vec![BracedStatementBlockExpression, caller_kind, Statement, Root]
        );
        assert_eq!(block.parent(), Some(caller.clone()));
        assert_braced_error_children(
            block,
            &[
                (LBrace, p..p + 1),
                (Whitespace, p + 1..p + 2),
                (Error, p + 2..p + 3),
                (Whitespace, p + 3..p + 4),
                (RBrace, p + 4..p + 5),
            ],
            false,
        );
        let body = block.children_with_tokens().collect::<Vec<_>>();
        for (child, text) in body.iter().zip(["{", " ", "@", " ", "}"]) {
            assert_eq!(child.as_token().unwrap().text(), text);
        }
        assert!(
            !root
                .descendants_with_tokens()
                .any(|child| matches!(child.kind(), Missing | Invalid))
        );
        assert_eq!(
            root.descendants()
                .filter(|node| node.kind() == Statement)
                .count(),
            1
        );
        assert_eq!(
            root.descendants_with_tokens()
                .filter(|child| child.kind() == Error)
                .count(),
            1
        );

        // The required-Statement phase and immediate block own this maximal
        // Error group; caller ancestry does not change its schema projection.
        let mut projected = Vec::new();
        let mut index = 1;
        while index + 1 < body.len() {
            if body[index].kind() != Error {
                assert_eq!(body[index].kind(), Whitespace);
                index += 1;
                continue;
            }
            let start = body[index].text_range().start();
            let mut end = start;
            while index < body.len() && body[index].kind() == Error {
                let token = body[index].as_token().unwrap();
                assert_eq!(token.parent(), Some(block.clone()));
                assert_eq!(token.text_range().start(), end);
                end = token.text_range().end();
                index += 1;
            }
            projected.push(structural_fact(
                StructuralKind::ErrorGroup,
                usize::from(start)..usize::from(end),
            ));
        }
        assert_eq!(
            projected,
            vec![structural_fact(StructuralKind::ErrorGroup, p + 2..p + 3,)]
        );
        let NormalizedExit::Complete(tail, line) = exit else {
            panic!("deferred: {source:?}")
        };
        assert_eq!(line, LineEntry::InLine);
        if caller_kind == ForStatement {
            assert_eq!(tail, Ok(()));
        } else {
            let Err(Either::Right(end)) = &tail else {
                panic!("EOF: {source:?}")
            };
            assert!(end.item.payload_view().is_eof());
        }

        assert_eq!(facts, projected, "{source:?}");
        let (again, repeated_facts, repeated_exit, repeated_suffix) = parse(&source, 0, None);
        assert_eq!(again, green);
        assert_eq!(repeated_facts, facts);
        assert_eq!(repeated_suffix, suffix);
        let NormalizedExit::Complete(repeated_tail, repeated_line) = repeated_exit else {
            panic!("repeated parse deferred: {source:?}")
        };
        assert_eq!(repeated_tail, tail);
        assert_eq!(repeated_line, line);
    }
}

#[test]
fn declaration_body_callers_return_protected_closes_with_leading() {
    for prefix in ["mod M ", "role R ", "impl T ", "act A ", "for x in xs "] {
        for leading in ["  ", "\r\n  "] {
            for close in [')', ']'] {
                let owned = format!("{prefix}{{x");
                let source = format!("{owned}{leading}{close}tail");
                let (green, facts, exit, suffix) = parse(&source, 100, None);
                assert_eq!(green.to_string(), owned, "{source:?}");
                let at = 100 + owned.len();
                assert_eq!(
                    facts,
                    [structural_fact(
                        StructuralKind::Missing,
                        owned.len()..owned.len(),
                    )],
                    "{source:?}"
                );
                let NormalizedExit::Complete(Err(Either::Left(item)), _) = exit else {
                    panic!("protected close: {source:?}")
                };
                assert_eq!(suffix, "tail");
                assert_eq!(
                    item.extent(100 + source.len() - suffix.len())
                        .recovery_range(),
                    at..at + leading.len() + 1
                );
                let (again, repeated_facts, _, remainder) = parse(&source, 100, None);
                assert_eq!(again, green);
                assert_eq!(repeated_facts, facts);
                assert_eq!(remainder, suffix);
            }
        }
    }
}

#[test]
fn error_run_stops_at_quoted_fence_and_qualifying_newline() {
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
    let source = "{ 💥\r\n> ```\nouter";
    let (green, facts, exit, suffix) = parse(source, 100, Some(&fence));
    assert_eq!(green.to_string(), "{ 💥");
    assert_eq!(
        facts,
        [
            structural_fact(StructuralKind::ErrorGroup, 2..6),
            structural_fact(StructuralKind::Missing, 6..6),
        ]
    );
    assert!(matches!(
        exit,
        NormalizedExit::Complete(Err(Either::Left(_)), _)
    ));
    assert_eq!(suffix, "> ```\nouter");
    let (again, repeated_facts, _, _) = parse(source, 100, Some(&fence));
    assert_eq!(again, green);
    assert_eq!(repeated_facts, facts);
    let (green, facts, _, _) = parse("{ @\n@ x}", 0, None);
    assert_eq!(green.to_string(), "{ @\n@ x}");
    assert_eq!(
        facts,
        [
            structural_fact(StructuralKind::ErrorGroup, 2..3),
            structural_fact(StructuralKind::ErrorGroup, 4..5),
        ]
    );
}

#[test]
fn optional_statement_rejection_is_effect_free() {
    let (green, facts, exit, suffix) = parse("@ rest", 0, None);
    assert_eq!(green.to_string(), "");
    assert!(facts.is_empty());
    assert!(matches!(
        exit,
        NormalizedExit::Complete(Err(Either::Left(_)), _)
    ));
    assert_eq!(suffix, " rest");
}

#[test]
fn braced_statement_raw_error_ordered_children() {
    use SyntaxKind::{BlockStatementSeparator, Error, LBrace, RBrace, Statement, Whitespace};

    for (source, direct) in [
        ("{@}", vec![(LBrace, 0..1), (Error, 1..2), (RBrace, 2..3)]),
        (
            "{@ use a}",
            vec![
                (LBrace, 0..1),
                (Error, 1..2),
                (Statement, 2..8),
                (RBrace, 8..9),
            ],
        ),
        (
            "{@,}",
            vec![
                (LBrace, 0..1),
                (Error, 1..2),
                (BlockStatementSeparator, 2..3),
                (RBrace, 3..4),
            ],
        ),
        (
            "{@; use a}",
            vec![
                (LBrace, 0..1),
                (Error, 1..2),
                (BlockStatementSeparator, 2..4),
                (Statement, 4..9),
                (RBrace, 9..10),
            ],
        ),
        (
            "{ @ @ α}",
            vec![
                (LBrace, 0..1),
                (Whitespace, 1..2),
                (Error, 2..3),
                (Error, 3..4),
                (Error, 4..5),
                (Statement, 5..8),
                (RBrace, 8..9),
            ],
        ),
        (
            "{💥\n💥 use a}",
            vec![
                (LBrace, 0..1),
                (Error, 1..5),
                (BlockStatementSeparator, 5..6),
                (Error, 6..10),
                (Statement, 10..16),
                (RBrace, 16..17),
            ],
        ),
        (
            "{@\r\n@ use a}",
            vec![
                (LBrace, 0..1),
                (Error, 1..2),
                (BlockStatementSeparator, 2..4),
                (Error, 4..5),
                (Statement, 5..11),
                (RBrace, 11..12),
            ],
        ),
    ] {
        let (green, facts, exit, suffix) = parse(source, 0, None);
        assert_eq!(green.to_string(), source);
        assert_eq!(suffix, "", "{source:?}");
        assert!(matches!(
            exit,
            NormalizedExit::Complete(Err(Either::Right(_)), _)
        ));
        let root = SyntaxNode::new_root(green.clone());
        let block = root
            .descendants()
            .find(|node| node.kind() == SyntaxKind::BracedStatementBlockExpression)
            .unwrap();
        assert_eq!(
            block
                .ancestors()
                .map(|node| node.kind())
                .collect::<Vec<_>>(),
            vec![
                SyntaxKind::BracedStatementBlockExpression,
                SyntaxKind::OperatorChain,
                Statement,
                SyntaxKind::Root,
            ],
            "{source:?}",
        );
        assert_braced_error_children(&block, &direct, false);
        assert!(
            !root
                .descendants_with_tokens()
                .any(|child| matches!(child.kind(), SyntaxKind::Missing | SyntaxKind::Invalid))
        );

        let children = block.children_with_tokens().collect::<Vec<_>>();
        let close = children.last().unwrap().as_token().unwrap();
        assert_eq!(close.kind(), RBrace);
        assert_eq!(close.text(), "}");
        assert_eq!(
            close.text_range(),
            rowan::TextRange::new(
                (source.len() as u32 - 1).into(),
                (source.len() as u32).into()
            )
        );

        // The direct sequence phase selects each structural occurrence.
        // Only adjacent Error tokens share an occurrence; a separator or retry
        // Statement ends it even when the next malformed slot has the same role.
        let mut projected = Vec::new();
        let mut required_statement = true;
        let mut index = 1;
        while index + 1 < children.len() {
            let child = &children[index];
            match child.kind() {
                Error => {
                    assert!(required_statement, "{source:?}");
                    let start = child.text_range().start();
                    let mut end = start;
                    while index < children.len() && children[index].kind() == Error {
                        let token = children[index].as_token().unwrap();
                        assert_eq!(token.text_range().start(), end);
                        end = token.text_range().end();
                        index += 1;
                    }
                    projected.push(structural_fact(
                        StructuralKind::ErrorGroup,
                        usize::from(start)..usize::from(end),
                    ));
                    continue;
                }
                Whitespace => {
                    assert_eq!(index, 1);
                    let leading = child.as_token().unwrap();
                    assert_eq!(leading.text(), " ");
                    assert_eq!(
                        leading.text_range(),
                        rowan::TextRange::new(1.into(), 2.into())
                    );
                }
                BlockStatementSeparator => {
                    let separator = child.as_node().unwrap();
                    let native = separator.children_with_tokens().collect::<Vec<_>>();
                    let expected = match source {
                        "{@,}" => vec![(SyntaxKind::Comma, ",")],
                        "{@; use a}" => vec![(SyntaxKind::Semicolon, ";"), (Whitespace, " ")],
                        "{💥\n💥 use a}" => vec![(SyntaxKind::Newline, "\n")],
                        "{@\r\n@ use a}" => vec![(SyntaxKind::Newline, "\r\n")],
                        _ => unreachable!(),
                    };
                    assert_eq!(native.len(), expected.len());
                    for (token, (kind, text)) in native.iter().zip(expected) {
                        assert_eq!(token.parent(), Some(separator.clone()));
                        let token = token.as_token().unwrap();
                        assert_eq!(token.kind(), kind);
                        assert_eq!(token.text(), text);
                    }
                    required_statement = true;
                }
                Statement => {
                    assert!(required_statement, "{source:?}");
                    let retry = child.as_node().unwrap();
                    let leading = retry.first_token().unwrap();
                    if source == "{@; use a}" {
                        // The explicit separator already owns this leading.
                        assert_eq!(leading.kind(), SyntaxKind::UseKw);
                    } else {
                        assert_eq!(leading.kind(), Whitespace);
                        assert_eq!(leading.text(), " ");
                        assert!(
                            leading
                                .parent()
                                .unwrap()
                                .ancestors()
                                .any(|node| node == *retry)
                        );
                        assert_eq!(leading.text_range().start(), child.text_range().start());
                        assert_eq!(leading.text_range().len(), 1.into());
                    }
                    required_statement = false;
                }
                _ => panic!("unexpected direct sequence child for {source:?}"),
            }
            index += 1;
        }
        let ranges = match source {
            "{@}" | "{@ use a}" | "{@,}" | "{@; use a}" => vec![1..2],
            "{ @ @ α}" => vec![2..5],
            "{💥\n💥 use a}" => vec![1..5, 6..10],
            "{@\r\n@ use a}" => vec![1..2, 4..5],
            _ => unreachable!(),
        };
        assert_eq!(
            projected,
            ranges
                .iter()
                .map(|range| structural_fact(StructuralKind::ErrorGroup, range.clone()))
                .collect::<Vec<_>>(),
            "{source:?}",
        );

        assert_eq!(facts, projected, "{source:?}");
        let (again, repeated_facts, repeated_exit, repeated_suffix) = parse(source, 0, None);
        assert_eq!(again, green, "{source:?}");
        assert_eq!(repeated_facts, facts, "{source:?}");
        assert_eq!(repeated_suffix, suffix, "{source:?}");
        assert!(matches!(
            repeated_exit,
            NormalizedExit::Complete(Err(Either::Right(_)), _)
        ));
    }
}

fn assert_braced_error_children(
    block: &SyntaxNode,
    expected: &[(SyntaxKind, Range<usize>)],
    prefix_only: bool,
) {
    let children = block.children_with_tokens().collect::<Vec<_>>();
    let inspected = if prefix_only {
        &children[..expected.len()]
    } else {
        &children[..]
    };
    assert_eq!(
        inspected
            .iter()
            .map(|child| (
                child.kind(),
                usize::from(child.text_range().start())..usize::from(child.text_range().end())
            ))
            .collect::<Vec<_>>(),
        expected,
    );
    for child in inspected {
        assert_eq!(child.parent(), Some(block.clone()));
        assert_eq!(
            child.as_node().is_some(),
            matches!(
                child.kind(),
                SyntaxKind::Statement | SyntaxKind::BlockStatementSeparator
            )
        );
    }
    assert!(
        !block
            .descendants()
            .any(|node| node.kind() == SyntaxKind::Invalid)
    );
}

#[test]
fn braced_statement_raw_error_terminal_prefixes() {
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
    for (source, boundary) in [
        ("{@", None),
        ("{@  ", None),
        ("{@  )tail", None),
        ("{@\r\n  ]tail", None),
        ("{@\r\n> ```\nouter", Some(&fence)),
    ] {
        let (green, facts, exit, suffix) = parse(source, 0, boundary);
        let root = SyntaxNode::new_root(green.clone());
        let block = root
            .descendants()
            .find(|node| node.kind() == SyntaxKind::BracedStatementBlockExpression)
            .unwrap();
        // Compose each prefix with its distinct terminal Close slot below.
        assert_braced_error_children(
            &block,
            &[(SyntaxKind::LBrace, 0..1), (SyntaxKind::Error, 1..2)],
            true,
        );
        assert_eq!(
            block
                .children_with_tokens()
                .filter(|child| child.kind() == SyntaxKind::Error)
                .map(|child| child.text_range())
                .collect::<Vec<_>>(),
            [rowan::TextRange::new(1.into(), 2.into())]
        );
        let owned = if boundary.is_some() || source.ends_with("tail") {
            "{@"
        } else {
            source
        };
        assert_eq!(green.to_string(), owned);
        let mut parent = root.clone();
        for kind in [
            SyntaxKind::Statement,
            SyntaxKind::OperatorChain,
            SyntaxKind::BracedStatementBlockExpression,
        ] {
            let children = parent.children_with_tokens().collect::<Vec<_>>();
            assert_eq!(children.len(), 1);
            let child = children[0].as_node().unwrap();
            assert_eq!(child.kind(), kind);
            assert_eq!(child.parent(), Some(parent.clone()));
            assert_eq!(child.text_range(), root.text_range());
            assert_eq!(child.text().to_string(), owned);
            parent = child.clone();
        }
        assert_eq!(parent, block);
        assert_eq!(root.kind(), SyntaxKind::Root);
        assert_eq!(root.parent(), None);
        assert_eq!(
            root.text_range(),
            rowan::TextRange::new(0.into(), (owned.len() as u32).into())
        );
        let mut direct = vec![(SyntaxKind::LBrace, 0..1), (SyntaxKind::Error, 1..2)];
        if owned.len() > 2 {
            direct.push((SyntaxKind::Whitespace, 2..4));
        }
        direct.push((SyntaxKind::Missing, owned.len()..owned.len()));
        let children = block.children_with_tokens().collect::<Vec<_>>();
        assert_eq!(children.len(), direct.len());
        for (child, (kind, range)) in children.iter().zip(&direct) {
            assert_eq!(child.kind(), *kind);
            assert_eq!(child.parent(), Some(block.clone()));
            assert_eq!(
                child.text_range(),
                rowan::TextRange::new((range.start as u32).into(), (range.end as u32).into())
            );
            if *kind == SyntaxKind::Missing {
                let missing = child.as_node().unwrap();
                assert!(missing.children_with_tokens().next().is_none());
                assert_eq!(missing.text().to_string(), "");
            } else {
                assert_eq!(child.as_token().unwrap().text(), &owned[range.clone()]);
            }
        }

        // Ordered direct children select an Error group followed by terminal
        // closing-brace Missing.
        let mut projected = Vec::new();
        let mut index = 1;
        while index < children.len() {
            let child = &children[index];
            match child.kind() {
                SyntaxKind::Error => {
                    let start = child.text_range().start();
                    let mut end = start;
                    while index < children.len() && children[index].kind() == SyntaxKind::Error {
                        let token = children[index].as_token().unwrap();
                        assert_eq!(token.text_range().start(), end);
                        end = token.text_range().end();
                        index += 1;
                    }
                    projected.push(structural_fact(
                        StructuralKind::ErrorGroup,
                        usize::from(start)..usize::from(end),
                    ));
                    continue;
                }
                SyntaxKind::Whitespace => {}
                SyntaxKind::Missing => {
                    assert_eq!(index + 1, children.len());
                    assert!(
                        !children
                            .iter()
                            .any(|child| child.kind() == SyntaxKind::RBrace)
                    );
                    projected.push(structural_fact(
                        StructuralKind::Missing,
                        usize::from(child.text_range().start())
                            ..usize::from(child.text_range().end()),
                    ));
                }
                _ => panic!("unexpected terminal child: {source:?}"),
            }
            index += 1;
        }
        assert_eq!(
            projected,
            vec![
                structural_fact(StructuralKind::ErrorGroup, 1..2),
                structural_fact(StructuralKind::Missing, owned.len()..owned.len()),
            ]
        );
        assert_eq!(
            root.descendants_with_tokens()
                .filter(|child| matches!(
                    child.kind(),
                    SyntaxKind::Error | SyntaxKind::Missing | SyntaxKind::Invalid
                ))
                .map(|child| (child.kind(), child.text_range()))
                .collect::<Vec<_>>(),
            vec![
                (SyntaxKind::Error, children[1].text_range()),
                (SyntaxKind::Missing, children.last().unwrap().text_range())
            ]
        );

        if boundary.is_some() {
            use crate::lexical::{
                item::{BorrowedTarget, Boundary, LeadingTrivia, Payload, PendingBoundary},
                yumark::{FenceCloseFacts, QuotePrefixFacts},
            };
            let inspect_fence_exit = |exit: NormalizedExit, suffix: &str| {
                let NormalizedExit::Complete(Err(Either::Left(item)), line_entry) = exit else {
                    panic!("protected fence handoff")
                };
                assert_eq!(line_entry, LineEntry::PhysicalStart);
                assert_eq!(suffix, "> ```\nouter");
                let expected_boundary = PendingBoundary::new(
                    4..10,
                    Boundary::BorrowedClose(BorrowedTarget::YumarkFence(Box::new(
                        FenceCloseFacts {
                            line: 4,
                            inspected: 4..10,
                            prefix: Some(QuotePrefixFacts {
                                indentation: 4..4,
                                marker: 4..5,
                                extent: 4..6,
                                depth: 1,
                                marker_len: 2,
                                marker_end: 1,
                                explicit: false,
                            }),
                            indentation: 6..6,
                            indentation_column: 0,
                            marker: 6..9,
                            marker_width: 3,
                            horizontal_suffix: 9..9,
                            newline: Some(9..10),
                        },
                    ))),
                );
                let pending = item
                    .payload_view()
                    .pending_boundary()
                    .expect("fence boundary");
                assert_eq!(pending.coordinate(), 4);
                assert_eq!(pending.inspected(), &(4..10));
                assert_eq!(pending, &expected_boundary);
                let extent = item.extent(4);
                assert_eq!(extent.physical(), 2..4);
                assert_eq!(extent.remaining(), 2..4);
                assert_eq!(extent.leading(), 2..4);
                assert_eq!(extent.payload(), 4..4);
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
                assert_eq!(format!("{green}{leading}{suffix}"), source);
            };
            inspect_fence_exit(exit, suffix);
            assert_eq!(facts, projected);
            let (again, repeated_facts, repeated_exit, repeated_suffix) =
                parse(source, 0, Some(&fence));
            assert_eq!(again, green);
            assert_eq!(repeated_facts, facts);
            inspect_fence_exit(repeated_exit, repeated_suffix);
            continue;
        }

        let inspect_exit = |exit: NormalizedExit, suffix: &str| {
            let NormalizedExit::Complete(exit, line_entry) = exit else {
                panic!("completed terminal handoff: {source:?}")
            };
            assert_eq!(line_entry, LineEntry::InLine);
            if owned == source {
                assert_eq!(suffix, "");
                let Err(Either::Right(end)) = exit else {
                    panic!("EOF handoff")
                };
                assert!(end.item.payload_view().is_eof());
                assert_eq!(
                    end.item.extent(source.len()).recovery_range(),
                    source.len()..source.len()
                );
            } else {
                assert_eq!(suffix, "tail");
                let Err(Either::Left(item)) = exit else {
                    panic!("protected close handoff")
                };
                let end = source.len() - suffix.len();
                assert_eq!(item.payload_view().spelling(), Some(&source[end - 1..end]));
                assert_eq!(
                    item.payload_view().token_kind(),
                    Some(if source.contains(')') {
                        crate::lexical::item::TokenKind::RParen
                    } else {
                        crate::lexical::item::TokenKind::RBracket
                    })
                );
                let extent = item.extent(end);
                assert_eq!(extent.recovery_range(), 2..end);
                assert_eq!(extent.leading(), 2..end - 1);
                assert_eq!(extent.payload(), end - 1..end);
                let mut leading = GreenNodeBuilder::new();
                leading.start_node(SyntaxKind::Root.into());
                let mut pending = item;
                pending.emit_all_remaining_leading(&mut leading);
                leading.finish_node();
                assert_eq!(leading.finish().to_string(), &source[2..end - 1]);
            }
        };
        inspect_exit(exit, suffix);
        assert_eq!(facts, projected);
        let (again, repeated_facts, repeated_exit, repeated_suffix) = parse(source, 0, None);
        assert_eq!(again, green);
        assert_eq!(repeated_facts, facts);
        inspect_exit(repeated_exit, repeated_suffix);
    }
}

#[test]
fn braced_statement_raw_error_stays_in_nested_for_body() {
    let source = "{for x in xs {@}; use a}";
    let (green, facts, exit, suffix) = parse(source, 0, None);
    assert_eq!(green.to_string(), source);
    assert_eq!(suffix, "");
    let root = SyntaxNode::new_root(green.clone());
    assert_eq!(root.kind(), SyntaxKind::Root);
    let root_children = root.children_with_tokens().collect::<Vec<_>>();
    assert_eq!(root_children.len(), 1);
    let root_statement = root_children[0].as_node().unwrap();
    assert_eq!(root_statement.kind(), SyntaxKind::Statement);
    let statement_children = root_statement.children_with_tokens().collect::<Vec<_>>();
    assert_eq!(statement_children.len(), 1);
    let chain = statement_children[0].as_node().unwrap();
    assert_eq!(chain.kind(), SyntaxKind::OperatorChain);
    let chain_children = chain.children_with_tokens().collect::<Vec<_>>();
    assert_eq!(chain_children.len(), 1);
    let outer = chain_children[0].as_node().unwrap();
    assert_eq!(outer.kind(), SyntaxKind::BracedStatementBlockExpression);
    assert_braced_error_children(
        outer,
        &[
            (SyntaxKind::LBrace, 0..1),
            (SyntaxKind::Statement, 1..16),
            (SyntaxKind::BlockStatementSeparator, 16..18),
            (SyntaxKind::Statement, 18..23),
            (SyntaxKind::RBrace, 23..24),
        ],
        false,
    );
    let outer_children = outer.children_with_tokens().collect::<Vec<_>>();
    let statement = outer_children[1].as_node().unwrap();
    let statement_children = statement.children_with_tokens().collect::<Vec<_>>();
    assert_eq!(statement_children.len(), 1);
    let for_statement = statement_children[0].as_node().unwrap();
    assert_eq!(for_statement.kind(), SyntaxKind::ForStatement);
    let nested = for_statement.children().last().unwrap();
    assert_eq!(nested.kind(), SyntaxKind::BracedStatementBlockExpression);
    assert_eq!(
        nested
            .ancestors()
            .map(|node| node.kind())
            .collect::<Vec<_>>(),
        vec![
            SyntaxKind::BracedStatementBlockExpression,
            SyntaxKind::ForStatement,
            SyntaxKind::Statement,
            SyntaxKind::BracedStatementBlockExpression,
            SyntaxKind::OperatorChain,
            SyntaxKind::Statement,
            SyntaxKind::Root,
        ]
    );
    assert_braced_error_children(
        &nested,
        &[
            (SyntaxKind::LBrace, 13..14),
            (SyntaxKind::Error, 14..15),
            (SyntaxKind::RBrace, 15..16),
        ],
        false,
    );
    let inner_children = nested.children_with_tokens().collect::<Vec<_>>();
    for (child, text) in inner_children.iter().zip(["{", "@", "}"]) {
        assert_eq!(child.as_token().unwrap().text(), text);
    }
    assert_eq!(outer_children[0].as_token().unwrap().text(), "{");
    assert_eq!(outer_children[4].as_token().unwrap().text(), "}");
    let separator = outer_children[2].as_node().unwrap();
    assert_eq!(
        separator
            .children_with_tokens()
            .map(|child| {
                let token = child.into_token().unwrap();
                (token.kind(), token.text().to_owned())
            })
            .collect::<Vec<_>>(),
        vec![
            (SyntaxKind::Semicolon, ";".to_owned()),
            (SyntaxKind::Whitespace, " ".to_owned()),
        ]
    );
    let use_statement = outer_children[3].as_node().unwrap();
    assert_ne!(use_statement, statement);
    let use_children = use_statement.children_with_tokens().collect::<Vec<_>>();
    assert_eq!(use_children.len(), 1);
    let use_declaration = use_children[0].as_node().unwrap();
    assert_eq!(use_declaration.kind(), SyntaxKind::UseDeclaration);
    assert_eq!(use_declaration.text().to_string(), "use a");
    assert_eq!(
        root.descendants_with_tokens()
            .filter(|child| matches!(
                child.kind(),
                SyntaxKind::Error | SyntaxKind::Missing | SyntaxKind::Invalid
            ))
            .collect::<Vec<_>>(),
        vec![inner_children[1].clone()]
    );

    // Interpret each block's direct slots independently: the accepted For
    // carries its child's recovery without adding one to the outer sequence.
    let mut projected = Vec::new();
    for (children, expected_count) in [(&outer_children, 0), (&inner_children, 1)] {
        let mut direct = Vec::new();
        let mut index = 1;
        while index + 1 < children.len() {
            if children[index].kind() != SyntaxKind::Error {
                index += 1;
                continue;
            }
            // This witness's only Error group starts in the required slot.
            assert_eq!(index, 1);
            let start = children[index].text_range().start();
            let mut end = start;
            while index < children.len() && children[index].kind() == SyntaxKind::Error {
                let token = children[index].as_token().unwrap();
                assert_eq!(token.text_range().start(), end);
                end = token.text_range().end();
                index += 1;
            }
            assert_eq!(children[index].kind(), SyntaxKind::RBrace);
            direct.push(structural_fact(
                StructuralKind::ErrorGroup,
                usize::from(start)..usize::from(end),
            ));
        }
        assert_eq!(direct.len(), expected_count);
        projected.extend(direct);
    }
    assert_eq!(
        projected,
        vec![structural_fact(StructuralKind::ErrorGroup, 14..15)]
    );
    let NormalizedExit::Complete(tail, line) = exit else {
        panic!("completed outer block")
    };
    assert_eq!(line, LineEntry::InLine);
    let Err(Either::Right(end)) = &tail else {
        panic!("outer EOF handoff")
    };
    assert!(end.item.payload_view().is_eof());
    assert_eq!(end.item.extent(source.len()).recovery_range(), 24..24);

    assert_eq!(facts, projected);
    let (again, repeated_facts, repeated_exit, repeated_suffix) = parse(source, 0, None);
    assert_eq!(again, green);
    assert_eq!(repeated_facts, facts);
    assert_eq!(repeated_suffix, suffix);
    let NormalizedExit::Complete(repeated_tail, repeated_line) = repeated_exit else {
        panic!("repeated parse completed outer block")
    };
    assert_eq!(repeated_tail, tail);
    assert_eq!(repeated_line, line);
}

#[test]
fn nested_for_braced_body_success_resumes_the_enclosing_sequence() {
    for (source, expected_facts) in [
        ("{for x in xs {}}", vec![]),
        (
            "{for x in xs {} use a}",
            vec![structural_fact(StructuralKind::Missing, 15..15)],
        ),
        ("{for x in xs {}; use a}", vec![]),
        ("{for x in xs {}, use a}", vec![]),
        ("{for x in xs {}\nuse a}", vec![]),
        ("{for x in xs {}\r\nuse a}", vec![]),
    ] {
        let (green, facts, exit, suffix) = parse(source, 0, None);
        assert_eq!(green.to_string(), source, "{source:?}");
        assert_eq!(facts, expected_facts, "{source:?}");
        assert!(matches!(
            exit,
            NormalizedExit::Complete(Err(Either::Right(_)), _)
        ));
        assert_eq!(suffix, "", "{source:?}");

        if matches!(source, "{for x in xs {}}" | "{for x in xs {} use a}") {
            let root = SyntaxNode::new_root(green.clone());
            let block = root
                .descendants()
                .find(|node| node.kind() == SyntaxKind::BracedStatementBlockExpression)
                .unwrap();
            let children = block.children_with_tokens().collect::<Vec<_>>();
            let expected_kinds = if source == "{for x in xs {}}" {
                vec![
                    SyntaxKind::LBrace,
                    SyntaxKind::Statement,
                    SyntaxKind::RBrace,
                ]
            } else {
                vec![
                    SyntaxKind::LBrace,
                    SyntaxKind::Statement,
                    SyntaxKind::Missing,
                    SyntaxKind::Statement,
                    SyntaxKind::RBrace,
                ]
            };
            assert_eq!(
                children
                    .iter()
                    .map(|child| child.kind())
                    .collect::<Vec<_>>(),
                expected_kinds,
                "{source:?}",
            );
            for child in &children {
                assert_eq!(child.parent(), Some(block.clone()));
                assert_eq!(
                    child.as_node().is_some(),
                    matches!(child.kind(), SyntaxKind::Statement | SyntaxKind::Missing),
                );
            }
            let close = children.last().unwrap().as_token().unwrap();
            assert_eq!(close.kind(), SyntaxKind::RBrace);
            assert_eq!(close.text(), "}");
            assert_eq!(
                close.text_range(),
                rowan::TextRange::new(
                    (source.len() as u32 - 1).into(),
                    (source.len() as u32).into()
                ),
            );
            assert!(
                !block
                    .descendants()
                    .any(|node| node.kind() == SyntaxKind::Invalid)
            );
            let nested = children[1]
                .as_node()
                .unwrap()
                .descendants()
                .find(|node| node.kind() == SyntaxKind::BracedStatementBlockExpression)
                .unwrap();
            assert_eq!(nested.text().to_string(), "{}");
            assert_eq!(
                nested
                    .children_with_tokens()
                    .map(|child| child.kind())
                    .collect::<Vec<_>>(),
                vec![SyntaxKind::LBrace, SyntaxKind::RBrace],
            );
            if source == "{for x in xs {} use a}" {
                let missing = children[2].as_node().unwrap();
                assert_eq!(missing.text_range(), rowan::TextRange::empty(15.into()));
                assert!(missing.children_with_tokens().next().is_none());
                assert_eq!(
                    missing
                        .ancestors()
                        .take(2)
                        .map(|node| node.kind())
                        .collect::<Vec<_>>(),
                    vec![
                        SyntaxKind::Missing,
                        SyntaxKind::BracedStatementBlockExpression
                    ],
                );
            }
        }

        let (again, repeated_facts, repeated_exit, repeated_suffix) = parse(source, 0, None);
        assert_eq!(again, green, "{source:?}");
        assert_eq!(repeated_facts, facts, "{source:?}");
        assert!(matches!(
            repeated_exit,
            NormalizedExit::Complete(Err(Either::Right(_)), _)
        ));
        assert_eq!(repeated_suffix, suffix, "{source:?}");
    }
}
