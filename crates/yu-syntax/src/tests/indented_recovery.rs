use crate::tests::support::*;
use crate::{ambient_claim::AmbientClaimView, recovery_record::*};
use std::{ops::Range, sync::Arc};

fn record(role: GrammarRole, kind: RecoveryKind, range: Range<usize>) -> CommittedRecoveryRecord {
    CommittedRecoveryRecord {
        id: DiagnosticId(0),
        site: RecoverySiteKey {
            role,
            range: range.clone(),
        },
        kind,
        unexpected: if kind == RecoveryKind::Missing {
            Arc::from([])
        } else {
            Arc::from([UnexpectedSyntax::Token {
                range: range.clone(),
                category: UnexpectedCategory::OtherCharacter,
            }])
        },
        expectations: Arc::from([SyntaxExpectation {
            role,
            expected: ExpectedSyntax::Statement,
            range,
            sources: ExpectationSources::COMMITTED_RECOVERY_RULE,
        }]),
        primary_expectation: 0,
    }
}

fn parse<'s>(
    source: &'s str,
    stops: Stops,
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
    let mut input = source;
    let mut recover = Recover::new_for_test(&operators);
    let mut output = frozen
        .map(|records| {
            recover = Recover::reconcile_for_test(recover.operators(), records);
            GreenNodeBuilder::new()
        })
        .unwrap_or_else(GreenNodeBuilder::new);
    output.start_node(SyntaxKind::Root.into());
    let exit = statement_normalized(
        crate::cursor::SyntaxIn::new(&mut input, &mut recover, &mut output),
        0,
        stops,
        origin,
        LineEntry::InLine,
        fence,
        Some(AmbientClaimView::root_statement(0)).into(),
        Some(crate::sequence::SequenceOwner::RootStatement),
    );
    output.finish_node();
    let (green, records) = (output.finish(), recover.finish_recoveries_for_test());
    (green, records, exit, input)
}

fn range(node: &SyntaxNode) -> Range<usize> {
    usize::from(node.text_range().start())..usize::from(node.text_range().end())
}

fn direct_elements(node: &SyntaxNode) -> Vec<(SyntaxKind, Range<usize>)> {
    node.children_with_tokens()
        .map(|element| {
            (
                element.kind(),
                usize::from(element.text_range().start())..usize::from(element.text_range().end()),
            )
        })
        .collect()
}

fn colon_indented_block(root: &SyntaxNode) -> SyntaxNode {
    assert_eq!(root.kind(), SyntaxKind::Root);
    let statements = root.children().collect::<Vec<_>>();
    assert_eq!(
        statements
            .iter()
            .map(|node| node.kind())
            .collect::<Vec<_>>(),
        [SyntaxKind::Statement]
    );
    let chains = statements[0].children().collect::<Vec<_>>();
    assert_eq!(
        chains.iter().map(|node| node.kind()).collect::<Vec<_>>(),
        [SyntaxKind::OperatorChain]
    );
    let chain = &chains[0];
    let tail = chain
        .children()
        .find(|node| node.kind() == SyntaxKind::ColonApplicationTail)
        .expect("ColonApplicationTail");
    assert_eq!(tail.parent(), Some(chain.clone()));
    let tail_children = tail.children_with_tokens().collect::<Vec<_>>();
    assert_eq!(
        tail_children
            .iter()
            .map(|element| element.kind())
            .collect::<Vec<_>>(),
        [SyntaxKind::Colon, SyntaxKind::IndentedStatementBlock]
    );
    let colon = tail_children[0].clone().into_token().expect("Colon token");
    assert_eq!(colon.parent(), Some(tail.clone()));
    let block = tail_children[1]
        .clone()
        .into_node()
        .expect("IndentedStatementBlock node");
    assert_eq!(block.parent(), Some(tail));
    block
}

#[test]
fn indented_fresh_and_frozen_missing_and_error_records() {
    for (prefix, role) in [
        (
            "f:",
            GrammarRole::ColonApplication(ColonApplicationRole::IndentedStatement),
        ),
        (
            "f with:",
            GrammarRole::WithBody(WithBodyRole::IndentedStatement),
        ),
    ] {
        for (body, kind, range) in [
            ("\n  ", RecoveryKind::Missing, 3..3),
            ("\n  @ @ x", RecoveryKind::Error, 3..6),
            ("\n  x\n  @ @ y", RecoveryKind::Error, 7..10),
        ] {
            let source = format!("{prefix}{body}");
            let range = range.start + prefix.len()..range.end + prefix.len();
            let (green, records, _, _) = parse(&source, 0, 0, None, None);
            assert_eq!(records, [record(role, kind, range)], "{source:?}");
            assert_eq!(green.to_string(), source);
            let (again, frozen, _, _) = parse(&source, 0, 0, None, Some(&records));
            assert_eq!(again, green);
            assert_eq!(frozen, records);
        }
    }
}

#[test]
fn indented_later_equal_indent_rowan_schema_covers_error_retry_and_control() {
    use SyntaxKind::*;

    let assert_children = |parent: &SyntaxNode, expected: &[(SyntaxKind, bool, Range<usize>)]| {
        let children = parent.children_with_tokens().collect::<Vec<_>>();
        assert_eq!(children.len(), expected.len());
        for (child, (kind, is_node, span)) in children.iter().zip(expected) {
            assert_eq!(child.kind(), *kind);
            assert_eq!(child.as_node().is_some(), *is_node);
            assert_eq!(child.parent(), Some(parent.clone()));
            assert_eq!(
                usize::from(child.text_range().start())..usize::from(child.text_range().end()),
                *span
            );
        }
    };

    for prefix in ["f:", "f with:"] {
        let p = prefix.len();
        for (suffix, error, retry) in [
            ("\n  x\n  y", false, false),
            ("\n  x\n  @ @", true, false),
            ("\n  x\n  @ @ y", true, true),
        ] {
            let source = format!("{prefix}{suffix}");
            let end = source.len();
            for origin in [0, 41] {
                let (green, records, exit, rest) = parse(&source, 0, origin, None, None);
                assert_eq!(green.to_string(), source);
                let root = SyntaxNode::new_root(green.clone());
                assert_eq!(root.kind(), Root);
                assert_eq!(range(&root), 0..end);
                assert_eq!(root.parent(), None);
                assert_children(&root, &[(Statement, true, 0..end)]);
                let statement = root.first_child().unwrap();
                assert_children(&statement, &[(OperatorChain, true, 0..end)]);
                let chain = statement.first_child().unwrap();
                let tail = chain.last_child().unwrap();
                let selected_role = match tail.kind() {
                    ColonApplicationTail => {
                        assert_children(
                            &chain,
                            &[
                                (IdentifierExpression, true, 0..1),
                                (ColonApplicationTail, true, 1..end),
                            ],
                        );
                        assert_children(
                            &tail,
                            &[(Colon, false, 1..2), (IndentedStatementBlock, true, 2..end)],
                        );
                        GrammarRole::ColonApplication(ColonApplicationRole::IndentedStatement)
                    }
                    WithBodyTail => {
                        assert_children(
                            &chain,
                            &[
                                (IdentifierExpression, true, 0..1),
                                (Whitespace, false, 1..2),
                                (WithBodyTail, true, 2..end),
                            ],
                        );
                        assert_children(
                            &tail,
                            &[
                                (WithKw, false, 2..6),
                                (Colon, false, 6..7),
                                (IndentedStatementBlock, true, 7..end),
                            ],
                        );
                        GrammarRole::WithBody(WithBodyRole::IndentedStatement)
                    }
                    other => panic!("unexpected indented caller: {other:?}"),
                };
                let block = tail.first_child().unwrap();
                let mut expected = vec![
                    (Newline, false, p..p + 1),
                    (Whitespace, false, p + 1..p + 3),
                    (Statement, true, p + 3..p + 4),
                    (BlockStatementSeparator, true, p + 4..p + 7),
                ];
                if error {
                    expected.extend([
                        (Error, false, p + 7..p + 8),
                        (Error, false, p + 8..p + 9),
                        (Error, false, p + 9..p + 10),
                    ]);
                }
                if !error || retry {
                    expected.push((Statement, true, if retry { p + 10 } else { p + 7 }..end));
                }
                assert_children(&block, &expected);
                let separator = block.children().nth(1).unwrap();
                assert_children(
                    &separator,
                    &[
                        (Newline, false, p + 4..p + 5),
                        (Whitespace, false, p + 5..p + 7),
                    ],
                );

                // The accepted first Statement and its native separator select
                // the later child slot under the verified caller ancestry.
                let mut occurrences: Vec<(GrammarRole, RecoveryKind, Range<usize>)> = Vec::new();
                let mut in_error = false;
                for child in block.children_with_tokens().skip(4) {
                    let span = usize::from(child.text_range().start())
                        ..usize::from(child.text_range().end());
                    if child.kind() == Error {
                        assert!(child.as_token().is_some());
                        if in_error {
                            let previous = &mut occurrences.last_mut().unwrap().2;
                            assert_eq!(previous.end, span.start);
                            previous.end = span.end;
                        } else {
                            occurrences.push((selected_role, RecoveryKind::Error, span));
                        }
                        in_error = true;
                    } else {
                        in_error = false;
                    }
                }
                assert_eq!(
                    occurrences,
                    if error {
                        vec![(selected_role, RecoveryKind::Error, p + 7..p + 10)]
                    } else {
                        vec![]
                    }
                );
                for element in root.descendants_with_tokens() {
                    let span = usize::from(element.text_range().start())
                        ..usize::from(element.text_range().end());
                    assert_eq!(element.to_string(), source[span]);
                    assert!(!matches!(element.kind(), Missing | Invalid));
                }
                for admitted in block.children().filter(|node| node.kind() == Statement) {
                    let span = range(&admitted);
                    assert_children(&admitted, &[(OperatorChain, true, span.clone())]);
                    let chain = admitted.first_child().unwrap();
                    assert_children(&chain, &[(IdentifierExpression, true, span.clone())]);
                    let expression = chain.first_child().unwrap();
                    if retry && span.start == p + 10 {
                        assert_children(
                            &expression,
                            &[
                                (Whitespace, false, p + 10..p + 11),
                                (Identifier, false, p + 11..p + 12),
                            ],
                        );
                        assert_eq!(
                            expression.first_token().unwrap().parent(),
                            Some(expression.clone())
                        );
                    } else {
                        assert_children(&expression, &[(Identifier, false, span)]);
                    }
                }
                let assert_eof = |exit, rest: &str| {
                    assert_eq!(rest, "");
                    let NormalizedExit::Complete(Err(Either::Right(mut eof)), line) = exit else {
                        panic!("expected ordinary EOF: {source:?}")
                    };
                    assert_eq!(line, LineEntry::InLine);
                    assert!(eof.item.payload_view().is_eof());
                    let end = origin + end;
                    let extent = eof.item.extent(end);
                    assert_eq!(extent.remaining(), end..end);
                    assert_eq!(extent.payload(), end..end);
                    assert_eq!(extent.recovery_range(), end..end);
                    assert_eq!(emit_pending_leading_text(&mut eof.item), "");
                };
                assert_eof(exit, rest);
                // Records remain separate compatibility evidence until migration.
                let expected_records = occurrences
                    .into_iter()
                    .map(|(role, kind, span)| {
                        record(role, kind, origin + span.start..origin + span.end)
                    })
                    .collect::<Vec<_>>();
                assert_eq!(records, expected_records);
                let (again, frozen, again_exit, again_rest) =
                    parse(&source, 0, origin, None, Some(&records));
                assert_eq!(again, green);
                assert_eq!(frozen, records);
                assert_eof(again_exit, again_rest);
            }
        }
    }
}

#[test]
fn indented_retry_admits_each_canonical_family_and_literal() {
    for body in [
        "x",
        "\"text\"",
        "\"\"\"raw\"\"\"",
        "~\"raw\"",
        "pub x = y",
        "use x",
        "struct X {}",
        "enum E;",
        "error E;",
        "role R;",
        "impl T;",
        "cast(x): T;",
        "act A;",
    ] {
        let source = format!("f:\n  @ @ {body}");
        let (green, records, _, _) = parse(&source, 0, 0, None, None);
        assert_eq!(green.to_string(), source);
        assert_eq!(
            records,
            [record(
                GrammarRole::ColonApplication(ColonApplicationRole::IndentedStatement),
                RecoveryKind::Error,
                5..8
            )],
            "{source:?}"
        );
    }
}

#[test]
fn indented_direct_callers_transport_their_own_role() {
    use DeclarationRole as D;
    for (head, role) in [
        (
            "if x:",
            GrammarRole::IfExpression(IfExpressionRole::IndentedStatement),
        ),
        (
            "if x: y else:",
            GrammarRole::IfExpression(IfExpressionRole::IndentedStatement),
        ),
        (
            "if x: y elsif z:",
            GrammarRole::IfExpression(IfExpressionRole::IndentedStatement),
        ),
        (
            "for x in xs:",
            GrammarRole::ForStatement(ForStatementRole::IndentedStatement),
        ),
        (
            "case x: y ->",
            GrammarRole::ColonApplication(ColonApplicationRole::IndentedStatement),
        ),
        (
            "catch x: y ->",
            GrammarRole::ColonApplication(ColonApplicationRole::IndentedStatement),
        ),
        (
            "my x =",
            GrammarRole::Declaration(D::Binding(BindingRole::IndentedStatement)),
        ),
        (
            "mod M:",
            GrammarRole::Declaration(D::Mod(ModRole::IndentedStatement)),
        ),
        (
            "role R:",
            GrammarRole::Declaration(D::Role(RoleDeclarationRole::IndentedStatement)),
        ),
        (
            "impl T:",
            GrammarRole::Declaration(D::Impl(ImplRole::IndentedStatement)),
        ),
        (
            "act A:",
            GrammarRole::Declaration(D::Act(ActDeclarationRole::IndentedStatement)),
        ),
        (
            "cast(x): T =",
            GrammarRole::Declaration(D::Cast(CastRole::IndentedStatement)),
        ),
    ] {
        let source = format!("{head}\n  @ x");
        let (green, records, _, _) = parse(&source, 0, 0, None, None);
        assert_eq!(green.to_string(), source, "{source:?}");
        assert_eq!(
            records,
            [record(
                role,
                RecoveryKind::Error,
                head.len() + 3..head.len() + 4
            )],
            "{source:?}"
        );
        let (again, frozen, _, _) = parse(&source, 0, 0, None, Some(&records));
        assert_eq!(again, green);
        assert_eq!(frozen, records);
    }
}

#[test]
fn indented_boundaries_preserve_pending_leading_and_line_entry() {
    use crate::lexical::stops::STOP_COMMA;
    for (source, stops, emitted, kind, range, pending, pending_start) in [
        (
            "f:\n  , x",
            STOP_COMMA,
            "f:",
            RecoveryKind::Missing,
            2..2,
            TokenKind::Comma,
            2,
        ),
        (
            "f:\n  ]",
            0,
            "f:",
            RecoveryKind::Missing,
            2..2,
            TokenKind::RBracket,
            2,
        ),
        (
            "f:\n  @ , x",
            STOP_COMMA,
            "f:\n  @",
            RecoveryKind::Error,
            5..6,
            TokenKind::Comma,
            6,
        ),
        (
            "f:\n  @ ]",
            0,
            "f:\n  @",
            RecoveryKind::Error,
            5..6,
            TokenKind::RBracket,
            6,
        ),
        (
            "f:\n  @\nout",
            0,
            "f:\n  @",
            RecoveryKind::Error,
            5..6,
            TokenKind::Identifier,
            6,
        ),
        (
            "f:\n  @\n  x\nout",
            0,
            "f:\n  @\n  x",
            RecoveryKind::Error,
            5..6,
            TokenKind::Identifier,
            10,
        ),
    ] {
        let (green, records, exit, rest) = parse(source, stops, 0, None, None);
        assert_eq!(green.to_string(), emitted, "{source:?}");
        assert_eq!(
            records,
            [record(
                GrammarRole::ColonApplication(ColonApplicationRole::IndentedStatement),
                kind,
                range
            )]
        );
        let NormalizedExit::Complete(Err(Either::Left(item)), line) = exit else {
            panic!("pending Item")
        };
        assert_eq!(token_kind(&item), Some(pending));
        assert_eq!(
            item.extent(source.len() - rest.len()).recovery_range(),
            pending_start..source.len() - rest.len()
        );
        assert_eq!(line, LineEntry::InLine);
    }
}

#[test]
fn indented_nested_admission_retains_the_nested_recovery_owner() {
    let source = "f:\n  g with:\n    @ x";
    let (green, records, _, _) = parse(source, 0, 0, None, None);
    assert_eq!(green.to_string(), source);
    assert_eq!(
        records,
        [record(
            GrammarRole::WithBody(WithBodyRole::IndentedStatement),
            RecoveryKind::Error,
            17..18
        )]
    );
    let (again, frozen, _, _) = parse(source, 0, 0, None, Some(&records));
    assert_eq!(again, green);
    assert_eq!(frozen, records);
}

#[test]
fn indented_if_companion_stops_before_and_after_error() {
    let role = GrammarRole::ColonApplication(ColonApplicationRole::IndentedStatement);
    for (source, emitted, kind, range, start) in [
        ("f:\n  else x", "f:", RecoveryKind::Missing, 2..2, 2),
        ("f:\n  @ else x", "f:\n  @", RecoveryKind::Error, 5..6, 6),
    ] {
        let (green, records, exit, rest) = parse(source, STOP_ELSE, 0, None, None);
        assert_eq!(green.to_string(), emitted);
        assert_eq!(records, [record(role, kind, range)]);
        let NormalizedExit::Complete(Err(Either::Left(item)), LineEntry::InLine) = exit else {
            panic!("If companion handoff")
        };
        assert_eq!(item.payload_view().spelling(), Some("else"));
        assert_eq!(
            item.extent(source.len() - rest.len())
                .recovery_range()
                .start,
            start
        );
    }
}

#[test]
fn indented_colon_rowan_schema_covers_missing_error_retry_and_native_leading() {
    let (green, _, _, _) = parse("f:\n  ", 0, 0, None, None);
    let block = colon_indented_block(&SyntaxNode::new_root(green));
    assert_eq!(range(&block), 2..5);
    assert_eq!(
        direct_elements(&block),
        [
            (SyntaxKind::Newline, 2..3),
            (SyntaxKind::Whitespace, 3..5),
            (SyntaxKind::Missing, 5..5),
        ]
    );

    let (green, _, _, _) = parse("f:\n  @ @", 0, 0, None, None);
    let block = colon_indented_block(&SyntaxNode::new_root(green));
    assert!(
        block
            .children_with_tokens()
            .filter(|element| element.kind() == SyntaxKind::Error)
            .all(|element| element.as_token().is_some())
    );
    assert_eq!(range(&block), 2..8);
    assert_eq!(
        direct_elements(&block),
        [
            (SyntaxKind::Newline, 2..3),
            (SyntaxKind::Whitespace, 3..5),
            (SyntaxKind::Error, 5..6),
            (SyntaxKind::Error, 6..7),
            (SyntaxKind::Error, 7..8),
        ]
    );
    assert!(!block.children().any(|node| {
        matches!(
            node.kind(),
            SyntaxKind::Missing | SyntaxKind::Statement | SyntaxKind::Invalid
        )
    }));

    let (green, _, _, _) = parse("f:\n  @ @ x", 0, 0, None, None);
    let block = colon_indented_block(&SyntaxNode::new_root(green));
    assert!(
        block
            .children_with_tokens()
            .filter(|element| element.kind() == SyntaxKind::Error)
            .all(|element| element.as_token().is_some())
    );
    assert_eq!(
        direct_elements(&block),
        [
            (SyntaxKind::Newline, 2..3),
            (SyntaxKind::Whitespace, 3..5),
            (SyntaxKind::Error, 5..6),
            (SyntaxKind::Error, 6..7),
            (SyntaxKind::Error, 7..8),
            (SyntaxKind::Statement, 8..10),
        ]
    );
    let retry = block.children().last().expect("retried Statement");
    assert_eq!(retry.kind(), SyntaxKind::Statement);
    assert_eq!(range(&retry), 8..10);
    let retry_leading = retry.first_token().expect("retry-leading Whitespace");
    assert_eq!(retry_leading.kind(), SyntaxKind::Whitespace);
    assert_eq!(
        usize::from(retry_leading.text_range().start())
            ..usize::from(retry_leading.text_range().end()),
        8..9
    );

    let (green, _, _, _) = parse("f:\n  x", 0, 0, None, None);
    let block = colon_indented_block(&SyntaxNode::new_root(green));
    assert_eq!(
        direct_elements(&block),
        [
            (SyntaxKind::Newline, 2..3),
            (SyntaxKind::Whitespace, 3..5),
            (SyntaxKind::Statement, 5..6),
        ]
    );
}

#[test]
fn indented_assignment_rowan_schema_covers_missing_error_retry_and_handoff() {
    use SyntaxKind::*;

    let assert_children = |parent: &SyntaxNode, expected: &[(SyntaxKind, bool, Range<usize>)]| {
        let children = parent.children_with_tokens().collect::<Vec<_>>();
        assert_eq!(children.len(), expected.len());
        for (child, (kind, is_node, span)) in children.iter().zip(expected) {
            assert_eq!(child.kind(), *kind);
            assert_eq!(child.as_node().is_some(), *is_node);
            assert_eq!(child.parent(), Some(parent.clone()));
            assert_eq!(
                usize::from(child.text_range().start())..usize::from(child.text_range().end()),
                *span
            );
        }
    };

    for (source, missing, error, statement_start, protected) in [
        ("x =\n  y", false, false, Some(6), false),
        ("x =\n  ", true, false, None, false),
        ("x =\n  @ @ y", false, true, Some(9), false),
        ("x =\n  @ @", false, true, None, false),
        ("x =\n  @ @ ]", false, true, None, true),
    ] {
        let owned_end = if protected { 9 } else { source.len() };
        let (green, records, exit, rest) = parse(source, 0, 0, None, None);
        assert_eq!(green.to_string(), source[..owned_end]);
        let root = SyntaxNode::new_root(green.clone());
        assert_eq!(root.kind(), Root);
        assert_eq!(range(&root), 0..owned_end);
        assert_eq!(root.parent(), None);
        assert_children(&root, &[(Statement, true, 0..owned_end)]);
        let statement = root.first_child().unwrap();
        assert_children(&statement, &[(OperatorChain, true, 0..owned_end)]);
        let chain = statement.first_child().unwrap();
        assert_children(
            &chain,
            &[
                (IdentifierExpression, true, 0..1),
                (Whitespace, false, 1..2),
                (AssignmentTail, true, 2..owned_end),
            ],
        );
        let tail = chain.last_child().unwrap();
        assert_children(
            &tail,
            &[
                (Equals, false, 2..3),
                (IndentedStatementBlock, true, 3..owned_end),
            ],
        );
        let block = tail.first_child().unwrap();
        // This exact ancestor/introducer path selects the Statement RHS slot,
        // before consulting the temporary recovery records for compatibility.
        let selected_role = GrammarRole::Assignment(AssignmentRole::IndentedStatement);
        let mut expected = vec![(Newline, false, 3..4), (Whitespace, false, 4..6)];
        if missing {
            expected.push((Missing, true, 6..6));
        }
        if error {
            expected.extend([
                (Error, false, 6..7),
                (Error, false, 7..8),
                (Error, false, 8..9),
            ]);
        }
        if let Some(start) = statement_start {
            expected.push((Statement, true, start..owned_end));
        }
        assert_children(&block, &expected);
        for element in root.descendants_with_tokens() {
            let span =
                usize::from(element.text_range().start())..usize::from(element.text_range().end());
            assert_eq!(element.to_string(), source[span]);
            assert_ne!(element.kind(), Invalid);
        }
        let missing_nodes = root
            .descendants()
            .filter(|node| node.kind() == Missing)
            .collect::<Vec<_>>();
        assert_eq!(missing_nodes.len(), usize::from(missing));
        for node in missing_nodes {
            assert_eq!(node.parent(), Some(block.clone()));
            assert_eq!(node.children_with_tokens().count(), 0);
        }
        let errors = root
            .descendants_with_tokens()
            .filter(|element| element.kind() == Error)
            .collect::<Vec<_>>();
        assert_eq!(errors.len(), if error { 3 } else { 0 });
        if error {
            for pair in errors.windows(2) {
                assert_eq!(pair[0].text_range().end(), pair[1].text_range().start());
            }
            assert_eq!(errors[0].text_range().start(), 6.into());
            assert_eq!(errors[2].text_range().end(), 9.into());
        }
        if statement_start == Some(9) {
            let retry = block.last_child().unwrap();
            let leading = retry.first_token().unwrap();
            assert_eq!(leading.kind(), Whitespace);
            assert_eq!(leading.text(), " ");
            assert_eq!(usize::from(leading.text_range().start()), 9);
            assert_eq!(usize::from(leading.text_range().end()), 10);
            assert!(
                leading
                    .parent()
                    .unwrap()
                    .ancestors()
                    .any(|node| node == retry)
            );
            assert_ne!(leading.parent(), Some(block.clone()));
        }

        let assert_handoff = |exit, rest: &str| {
            assert_eq!(rest, "");
            let mut item = match exit {
                NormalizedExit::Complete(Err(Either::Left(item)), line) if protected => {
                    assert_eq!(line, LineEntry::InLine);
                    assert_eq!(token_kind(&item), Some(TokenKind::RBracket));
                    assert_eq!(item.payload_view().spelling(), Some("]"));
                    item
                }
                NormalizedExit::Complete(Err(Either::Right(end)), line) if !protected => {
                    assert_eq!(line, LineEntry::InLine);
                    assert!(end.item.payload_view().is_eof());
                    end.item
                }
                _ => panic!("expected exact EOF or protected-close handoff: {source:?}"),
            };
            let extent = item.extent(source.len());
            let leading = if protected {
                9..10
            } else {
                source.len()..source.len()
            };
            let payload = if protected {
                10..11
            } else {
                source.len()..source.len()
            };
            if protected {
                assert_eq!(extent.physical(), 9..11);
                assert_eq!(extent.leading(), 9..10);
            }
            assert_eq!(extent.remaining(), leading);
            assert_eq!(extent.payload(), payload.clone());
            assert_eq!(extent.recovery_range(), owned_end..source.len());
            assert_eq!(
                emit_pending_leading_text(&mut item),
                if protected { " " } else { "" }
            );
            let emitted = item.extent(source.len());
            if protected {
                assert_eq!(emitted.physical(), 9..11);
                assert_eq!(emitted.leading(), 9..10);
            }
            assert_eq!(emitted.remaining(), payload.start..payload.start);
            assert_eq!(emitted.payload(), payload.clone());
            assert_eq!(emitted.recovery_range(), payload);
        };
        assert_handoff(exit, rest);
        let expected_records = if missing {
            vec![record(selected_role, RecoveryKind::Missing, 6..6)]
        } else if error {
            vec![record(selected_role, RecoveryKind::Error, 6..9)]
        } else {
            vec![]
        };
        assert_eq!(records, expected_records);
        let (again, frozen, again_exit, again_rest) = parse(source, 0, 0, None, Some(&records));
        assert_eq!(again, green);
        assert_eq!(frozen, records);
        assert_handoff(again_exit, again_rest);
    }
}

#[test]
fn indented_with_rowan_schema_covers_first_statement_missing_error_retry_and_control() {
    use SyntaxKind::*;

    let assert_children = |parent: &SyntaxNode, expected: &[(SyntaxKind, bool, Range<usize>)]| {
        let children = parent.children_with_tokens().collect::<Vec<_>>();
        assert_eq!(children.len(), expected.len());
        for (child, (kind, is_node, span)) in children.iter().zip(expected) {
            assert_eq!(child.kind(), *kind);
            assert_eq!(child.as_node().is_some(), *is_node);
            assert_eq!(child.parent(), Some(parent.clone()));
            assert_eq!(
                usize::from(child.text_range().start())..usize::from(child.text_range().end()),
                *span
            );
        }
    };

    for (source, missing, error, statement_start) in [
        ("f with:\n  ", true, false, None),
        ("f with:\n  @ @", false, true, None),
        ("f with:\n  @ @ x", false, true, Some(13)),
        ("f with:\n  x", false, false, Some(10)),
    ] {
        let end = source.len();
        let (green, records, exit, rest) = parse(source, 0, 0, None, None);
        assert_eq!(green.to_string(), source);
        let root = SyntaxNode::new_root(green.clone());
        assert_eq!(root.kind(), Root);
        assert_eq!(range(&root), 0..end);
        assert_eq!(root.parent(), None);
        assert_children(&root, &[(Statement, true, 0..end)]);
        let statement = root.first_child().unwrap();
        assert_children(&statement, &[(OperatorChain, true, 0..end)]);
        let chain = statement.first_child().unwrap();
        assert_children(
            &chain,
            &[
                (IdentifierExpression, true, 0..1),
                (Whitespace, false, 1..2),
                (WithBodyTail, true, 2..end),
            ],
        );
        let identifier = chain.first_child().unwrap();
        assert_children(&identifier, &[(Identifier, false, 0..1)]);
        let tail = chain.last_child().unwrap();
        assert_children(
            &tail,
            &[
                (WithKw, false, 2..6),
                (Colon, false, 6..7),
                (IndentedStatementBlock, true, 7..end),
            ],
        );
        let block = tail.first_child().unwrap();
        // The verified With ancestor and actual Colon select this first
        // required Statement slot without inspecting Error spelling or records.
        let selected_role = GrammarRole::WithBody(WithBodyRole::IndentedStatement);
        let mut expected = vec![(Newline, false, 7..8), (Whitespace, false, 8..10)];
        if missing {
            expected.push((Missing, true, 10..10));
        }
        if error {
            expected.extend([
                (Error, false, 10..11),
                (Error, false, 11..12),
                (Error, false, 12..13),
            ]);
        }
        if let Some(start) = statement_start {
            expected.push((Statement, true, start..end));
        }
        assert_children(&block, &expected);
        for element in root.descendants_with_tokens() {
            let span =
                usize::from(element.text_range().start())..usize::from(element.text_range().end());
            assert_eq!(element.to_string(), source[span]);
            assert_ne!(element.kind(), Invalid);
        }
        let missing_nodes = root
            .descendants()
            .filter(|node| node.kind() == Missing)
            .collect::<Vec<_>>();
        assert_eq!(missing_nodes.len(), usize::from(missing));
        for node in missing_nodes {
            assert_eq!(node.parent(), Some(block.clone()));
            assert_eq!(node.children_with_tokens().count(), 0);
        }
        let errors = root
            .descendants_with_tokens()
            .filter(|element| element.kind() == Error)
            .collect::<Vec<_>>();
        assert_eq!(errors.len(), if error { 3 } else { 0 });

        // Derive occurrences from this slot's immediate children. Only adjacent
        // Error tokens coalesce; native trivia or a node ends the raw group.
        let mut occurrences = Vec::new();
        let mut in_error = false;
        for child in block.children_with_tokens() {
            let span =
                usize::from(child.text_range().start())..usize::from(child.text_range().end());
            if child.kind() == Error {
                assert!(child.as_token().is_some());
                if in_error {
                    let (_, _, previous): &mut (_, _, Range<usize>) =
                        occurrences.last_mut().unwrap();
                    assert_eq!(previous.end, span.start);
                    previous.end = span.end;
                } else {
                    occurrences.push((selected_role, RecoveryKind::Error, span));
                }
                in_error = true;
            } else {
                in_error = false;
                if child.kind() == Missing {
                    occurrences.push((selected_role, RecoveryKind::Missing, span));
                }
            }
        }
        let expected_occurrences = if missing {
            vec![(selected_role, RecoveryKind::Missing, 10..10)]
        } else if error {
            vec![(selected_role, RecoveryKind::Error, 10..13)]
        } else {
            vec![]
        };
        assert_eq!(occurrences, expected_occurrences);
        if statement_start == Some(13) {
            let retry = block.last_child().unwrap();
            let leading = retry.first_token().unwrap();
            assert_eq!(leading.kind(), Whitespace);
            assert_eq!(leading.text(), " ");
            assert_eq!(usize::from(leading.text_range().start()), 13);
            assert_eq!(usize::from(leading.text_range().end()), 14);
            assert!(
                leading
                    .parent()
                    .unwrap()
                    .ancestors()
                    .any(|node| node == retry)
            );
            assert_ne!(leading.parent(), Some(block.clone()));
        }

        let assert_eof = |exit, rest: &str| {
            assert_eq!(rest, "");
            let NormalizedExit::Complete(Err(Either::Right(mut eof)), line) = exit else {
                panic!("expected ordinary EOF: {source:?}")
            };
            assert_eq!(line, LineEntry::InLine);
            assert!(eof.item.payload_view().is_eof());
            let extent = eof.item.extent(end);
            assert_eq!(extent.remaining(), end..end);
            assert_eq!(extent.payload(), end..end);
            assert_eq!(extent.recovery_range(), end..end);
            assert_eq!(emit_pending_leading_text(&mut eof.item), "");
        };
        assert_eof(exit, rest);
        // Temporary records are compatibility evidence, not the slot selector.
        let expected_records = expected_occurrences
            .into_iter()
            .map(|(role, kind, span)| record(role, kind, span))
            .collect::<Vec<_>>();
        assert_eq!(records, expected_records);
        let (again, frozen, again_exit, again_rest) = parse(source, 0, 0, None, Some(&records));
        assert_eq!(again, green);
        assert_eq!(frozen, records);
        assert_eof(again_exit, again_rest);
    }
}

#[test]
fn indented_binding_rowan_schema_covers_first_statement_missing_error_retry_and_control() {
    use SyntaxKind::*;

    let assert_children = |parent: &SyntaxNode, expected: &[(SyntaxKind, bool, Range<usize>)]| {
        let children = parent.children_with_tokens().collect::<Vec<_>>();
        assert_eq!(children.len(), expected.len());
        for (child, (kind, is_node, span)) in children.iter().zip(expected) {
            assert_eq!(child.kind(), *kind);
            assert_eq!(child.as_node().is_some(), *is_node);
            assert_eq!(child.parent(), Some(parent.clone()));
            assert_eq!(
                usize::from(child.text_range().start())..usize::from(child.text_range().end()),
                *span
            );
        }
    };

    for (source, missing, error, statement_start) in [
        ("my x =\n  ", true, false, None),
        ("my x =\n  @ @", false, true, None),
        ("my x =\n  @ @ value", false, true, Some(12)),
        ("my x =\n  value", false, false, Some(9)),
    ] {
        let end = source.len();
        let (green, records, exit, rest) = parse(source, 0, 0, None, None);
        assert_eq!(green.to_string(), source);
        let root = SyntaxNode::new_root(green.clone());
        assert_eq!(root.kind(), Root);
        assert_eq!(range(&root), 0..end);
        assert_eq!(root.parent(), None);
        assert_children(&root, &[(Statement, true, 0..end)]);
        let statement = root.first_child().unwrap();
        assert_children(&statement, &[(BindingStatement, true, 0..end)]);
        let binding = statement.first_child().unwrap();
        assert_children(
            &binding,
            &[(BindingHeader, true, 0..6), (BindingBody, true, 6..end)],
        );
        let header = binding.first_child().unwrap();
        assert_children(
            &header,
            &[
                (MyKw, false, 0..2),
                (Whitespace, false, 2..3),
                (Pattern, true, 3..4),
                (Whitespace, false, 4..5),
                (Equals, false, 5..6),
            ],
        );
        let pattern = header.first_child().unwrap();
        assert_children(&pattern, &[(IdentifierPattern, true, 3..4)]);
        let identifier = pattern.first_child().unwrap();
        assert_children(&identifier, &[(Identifier, false, 3..4)]);
        let body = binding.last_child().unwrap();
        assert_children(&body, &[(IndentedStatementBlock, true, 6..end)]);
        let block = body.first_child().unwrap();
        // The verified Binding ancestor, accepted Header Equals and indented
        // Body select this first required Statement slot without Error spelling
        // or temporary records selecting its role.
        let selected_role =
            GrammarRole::Declaration(DeclarationRole::Binding(BindingRole::IndentedStatement));
        let mut expected = vec![(Newline, false, 6..7), (Whitespace, false, 7..9)];
        if missing {
            expected.push((Missing, true, 9..9));
        }
        if error {
            expected.extend([
                (Error, false, 9..10),
                (Error, false, 10..11),
                (Error, false, 11..12),
            ]);
        }
        if let Some(start) = statement_start {
            expected.push((Statement, true, start..end));
        }
        assert_children(&block, &expected);
        if let Some(start) = statement_start {
            let admitted = block.last_child().unwrap();
            assert_children(&admitted, &[(OperatorChain, true, start..end)]);
            let chain = admitted.first_child().unwrap();
            assert_children(&chain, &[(IdentifierExpression, true, start..end)]);
            let expression = chain.first_child().unwrap();
            if error {
                assert_children(
                    &expression,
                    &[(Whitespace, false, 12..13), (Identifier, false, 13..18)],
                );
                assert_ne!(
                    expression.first_token().unwrap().parent(),
                    Some(block.clone())
                );
            } else {
                assert_children(&expression, &[(Identifier, false, 9..14)]);
            }
        }
        for element in root.descendants_with_tokens() {
            let span =
                usize::from(element.text_range().start())..usize::from(element.text_range().end());
            assert_eq!(element.to_string(), source[span]);
            assert_ne!(element.kind(), Invalid);
        }
        let missing_nodes = root
            .descendants()
            .filter(|node| node.kind() == Missing)
            .collect::<Vec<_>>();
        assert_eq!(missing_nodes.len(), usize::from(missing));
        for node in missing_nodes {
            assert_eq!(node.parent(), Some(block.clone()));
            assert_eq!(node.children_with_tokens().count(), 0);
        }
        let errors = root
            .descendants_with_tokens()
            .filter(|element| element.kind() == Error)
            .collect::<Vec<_>>();
        assert_eq!(errors.len(), if error { 3 } else { 0 });

        // Derive occurrences from this slot's immediate children. Only adjacent
        // Error tokens coalesce; native trivia or a node ends the raw group.
        let mut occurrences = Vec::new();
        let mut in_error = false;
        for child in block.children_with_tokens() {
            let span =
                usize::from(child.text_range().start())..usize::from(child.text_range().end());
            if child.kind() == Error {
                assert!(child.as_token().is_some());
                if in_error {
                    let (_, _, previous): &mut (_, _, Range<usize>) =
                        occurrences.last_mut().unwrap();
                    assert_eq!(previous.end, span.start);
                    previous.end = span.end;
                } else {
                    occurrences.push((selected_role, RecoveryKind::Error, span));
                }
                in_error = true;
            } else {
                in_error = false;
                if child.kind() == Missing {
                    occurrences.push((selected_role, RecoveryKind::Missing, span));
                }
            }
        }
        let expected_occurrences = if missing {
            vec![(selected_role, RecoveryKind::Missing, 9..9)]
        } else if error {
            vec![(selected_role, RecoveryKind::Error, 9..12)]
        } else {
            vec![]
        };
        assert_eq!(occurrences, expected_occurrences);

        let assert_eof = |exit, rest: &str| {
            assert_eq!(rest, "");
            let NormalizedExit::Complete(Err(Either::Right(mut eof)), line) = exit else {
                panic!("expected ordinary EOF: {source:?}")
            };
            assert_eq!(line, LineEntry::InLine);
            assert!(eof.item.payload_view().is_eof());
            let extent = eof.item.extent(end);
            assert_eq!(extent.remaining(), end..end);
            assert_eq!(extent.payload(), end..end);
            assert_eq!(extent.recovery_range(), end..end);
            assert_eq!(emit_pending_leading_text(&mut eof.item), "");
        };
        assert_eof(exit, rest);
        // Temporary records are compatibility evidence, not the slot selector.
        // This slot expects Statement with primary alternative zero.
        let expected_records = expected_occurrences
            .into_iter()
            .map(|(role, kind, span)| record(role, kind, span))
            .collect::<Vec<_>>();
        assert_eq!(records, expected_records);
        let (again, frozen, again_exit, again_rest) = parse(source, 0, 0, None, Some(&records));
        assert_eq!(again, green);
        assert_eq!(frozen, records);
        assert_eof(again_exit, again_rest);
    }
}

#[test]
fn indented_mod_rowan_schema_covers_first_statement_missing_error_retry_and_control() {
    use SyntaxKind::*;

    let assert_children = |parent: &SyntaxNode, expected: &[(SyntaxKind, bool, Range<usize>)]| {
        let children = parent.children_with_tokens().collect::<Vec<_>>();
        assert_eq!(children.len(), expected.len());
        for (child, (kind, is_node, span)) in children.iter().zip(expected) {
            assert_eq!(child.kind(), *kind);
            assert_eq!(child.as_node().is_some(), *is_node);
            assert_eq!(child.parent(), Some(parent.clone()));
            assert_eq!(
                usize::from(child.text_range().start())..usize::from(child.text_range().end()),
                *span
            );
        }
    };

    for (source, missing, error, statement_start) in [
        ("mod M:\n  ", true, false, None),
        ("mod M:\n  @ @", false, true, None),
        ("mod M:\n  @ @ value", false, true, Some(12)),
        ("mod M:\n  value", false, false, Some(9)),
    ] {
        let end = source.len();
        let (green, records, exit, rest) = parse(source, 0, 0, None, None);
        assert_eq!(green.to_string(), source);
        let root = SyntaxNode::new_root(green.clone());
        assert_eq!(root.kind(), Root);
        assert_eq!(range(&root), 0..end);
        assert_eq!(root.parent(), None);
        assert_children(&root, &[(Statement, true, 0..end)]);
        let statement = root.first_child().unwrap();
        assert_children(&statement, &[(ModDeclaration, true, 0..end)]);
        let declaration = statement.first_child().unwrap();
        assert_children(
            &declaration,
            &[
                (ModKw, false, 0..3),
                (Whitespace, false, 3..4),
                (Identifier, false, 4..5),
                (Colon, false, 5..6),
                (IndentedStatementBlock, true, 6..end),
            ],
        );
        let block = declaration.first_child().unwrap();
        // The verified ordinary Mod ancestor, actual Colon and indented block
        // select this first required Statement slot without Error spelling or
        // temporary records selecting its role.
        let selected_role =
            GrammarRole::Declaration(DeclarationRole::Mod(ModRole::IndentedStatement));
        let mut expected = vec![(Newline, false, 6..7), (Whitespace, false, 7..9)];
        if missing {
            expected.push((Missing, true, 9..9));
        }
        if error {
            expected.extend([
                (Error, false, 9..10),
                (Error, false, 10..11),
                (Error, false, 11..12),
            ]);
        }
        if let Some(start) = statement_start {
            expected.push((Statement, true, start..end));
        }
        assert_children(&block, &expected);
        if let Some(start) = statement_start {
            let admitted = block.last_child().unwrap();
            assert_children(&admitted, &[(OperatorChain, true, start..end)]);
            let chain = admitted.first_child().unwrap();
            assert_children(&chain, &[(IdentifierExpression, true, start..end)]);
            let expression = chain.first_child().unwrap();
            if error {
                assert_children(
                    &expression,
                    &[(Whitespace, false, 12..13), (Identifier, false, 13..18)],
                );
                assert_ne!(
                    expression.first_token().unwrap().parent(),
                    Some(block.clone())
                );
            } else {
                assert_children(&expression, &[(Identifier, false, 9..14)]);
            }
        }
        for element in root.descendants_with_tokens() {
            let span =
                usize::from(element.text_range().start())..usize::from(element.text_range().end());
            assert_eq!(element.to_string(), source[span]);
            assert_ne!(element.kind(), Invalid);
        }
        let missing_nodes = root
            .descendants()
            .filter(|node| node.kind() == Missing)
            .collect::<Vec<_>>();
        assert_eq!(missing_nodes.len(), usize::from(missing));
        for node in missing_nodes {
            assert_eq!(node.parent(), Some(block.clone()));
            assert_eq!(node.children_with_tokens().count(), 0);
        }
        let errors = root
            .descendants_with_tokens()
            .filter(|element| element.kind() == Error)
            .collect::<Vec<_>>();
        assert_eq!(errors.len(), if error { 3 } else { 0 });

        // Derive occurrences from this slot's immediate children. Only adjacent
        // Error tokens coalesce; native trivia or a node ends the raw group.
        let mut occurrences = Vec::new();
        let mut in_error = false;
        for child in block.children_with_tokens() {
            let span =
                usize::from(child.text_range().start())..usize::from(child.text_range().end());
            if child.kind() == Error {
                assert!(child.as_token().is_some());
                if in_error {
                    let (_, _, previous): &mut (_, _, Range<usize>) =
                        occurrences.last_mut().unwrap();
                    assert_eq!(previous.end, span.start);
                    previous.end = span.end;
                } else {
                    occurrences.push((selected_role, RecoveryKind::Error, span));
                }
                in_error = true;
            } else {
                in_error = false;
                if child.kind() == Missing {
                    occurrences.push((selected_role, RecoveryKind::Missing, span));
                }
            }
        }
        let expected_occurrences = if missing {
            vec![(selected_role, RecoveryKind::Missing, 9..9)]
        } else if error {
            vec![(selected_role, RecoveryKind::Error, 9..12)]
        } else {
            vec![]
        };
        assert_eq!(occurrences, expected_occurrences);

        let assert_eof = |exit, rest: &str| {
            assert_eq!(rest, "");
            let NormalizedExit::Complete(Err(Either::Right(mut eof)), line) = exit else {
                panic!("expected ordinary EOF: {source:?}")
            };
            assert_eq!(line, LineEntry::InLine);
            assert!(eof.item.payload_view().is_eof());
            let extent = eof.item.extent(end);
            assert_eq!(extent.remaining(), end..end);
            assert_eq!(extent.payload(), end..end);
            assert_eq!(extent.recovery_range(), end..end);
            assert_eq!(emit_pending_leading_text(&mut eof.item), "");
        };
        assert_eof(exit, rest);
        // Temporary records are compatibility evidence, not the slot selector.
        // This slot expects Statement with primary alternative zero.
        let expected_records = expected_occurrences
            .into_iter()
            .map(|(role, kind, span)| record(role, kind, span))
            .collect::<Vec<_>>();
        assert_eq!(records, expected_records);
        let (again, frozen, again_exit, again_rest) = parse(source, 0, 0, None, Some(&records));
        assert_eq!(again, green);
        assert_eq!(frozen, records);
        assert_eof(again_exit, again_rest);
    }
}

#[test]
fn indented_role_rowan_schema_covers_first_statement_missing_error_retry_and_control() {
    use SyntaxKind::*;

    let assert_children = |parent: &SyntaxNode, expected: &[(SyntaxKind, bool, Range<usize>)]| {
        let children = parent.children_with_tokens().collect::<Vec<_>>();
        assert_eq!(children.len(), expected.len());
        for (child, (kind, is_node, span)) in children.iter().zip(expected) {
            assert_eq!(child.kind(), *kind);
            assert_eq!(child.as_node().is_some(), *is_node);
            assert_eq!(child.parent(), Some(parent.clone()));
            assert_eq!(
                usize::from(child.text_range().start())..usize::from(child.text_range().end()),
                *span
            );
        }
    };

    for origin in [0, 41] {
        for (source, missing, error, statement_start) in [
            ("role R:\n  ", true, false, None),
            ("role R:\n  @ @", false, true, None),
            ("role R:\n  @ @ value", false, true, Some(13)),
            ("role R:\n  value", false, false, Some(10)),
        ] {
            let end = source.len();
            let (green, records, exit, rest) = parse(source, 0, origin, None, None);
            assert_eq!(green.to_string(), source);
            let root = SyntaxNode::new_root(green.clone());
            assert_eq!(root.kind(), Root);
            assert_eq!(range(&root), 0..end);
            assert_eq!(root.parent(), None);
            assert_children(&root, &[(Statement, true, 0..end)]);
            let statement = root.first_child().unwrap();
            assert_children(&statement, &[(RoleDeclaration, true, 0..end)]);
            let declaration = statement.first_child().unwrap();
            assert_children(
                &declaration,
                &[
                    (RoleKw, false, 0..4),
                    (Whitespace, false, 4..5),
                    (TypeExpression, true, 5..6),
                    (Colon, false, 6..7),
                    (IndentedStatementBlock, true, 7..end),
                ],
            );
            let head = declaration.first_child().unwrap();
            assert_eq!(head.to_string(), "R");
            let block = declaration.last_child().unwrap();
            // Completed direct Head, actual Colon and this Role-owned block
            // select the first Statement slot independently of recovery records.
            let selected_role = GrammarRole::Declaration(DeclarationRole::Role(
                RoleDeclarationRole::IndentedStatement,
            ));
            let mut expected = vec![(Newline, false, 7..8), (Whitespace, false, 8..10)];
            if missing {
                expected.push((Missing, true, 10..10));
            }
            if error {
                expected.extend([
                    (Error, false, 10..11),
                    (Error, false, 11..12),
                    (Error, false, 12..13),
                ]);
            }
            if let Some(start) = statement_start {
                expected.push((Statement, true, start..end));
            }
            assert_children(&block, &expected);
            if let Some(start) = statement_start {
                let admitted = block.last_child().unwrap();
                assert_children(&admitted, &[(OperatorChain, true, start..end)]);
                let chain = admitted.first_child().unwrap();
                assert_children(&chain, &[(IdentifierExpression, true, start..end)]);
                let expression = chain.first_child().unwrap();
                if error {
                    assert_children(
                        &expression,
                        &[(Whitespace, false, 13..14), (Identifier, false, 14..19)],
                    );
                } else {
                    assert_children(&expression, &[(Identifier, false, 10..15)]);
                }
            }
            for element in root.descendants_with_tokens() {
                let span = usize::from(element.text_range().start())
                    ..usize::from(element.text_range().end());
                assert_eq!(element.to_string(), source[span]);
                assert_ne!(element.kind(), Invalid);
                if element.kind() == Missing {
                    let node = element.as_node().expect("empty Missing node");
                    assert_eq!(node.parent(), Some(block.clone()));
                    assert_eq!(node.children_with_tokens().count(), 0);
                }
            }
            for (kind, count) in [
                (Missing, usize::from(missing)),
                (Error, if error { 3 } else { 0 }),
            ] {
                assert_eq!(
                    root.descendants_with_tokens()
                        .filter(|element| element.kind() == kind)
                        .count(),
                    count
                );
            }

            // Only adjacent Error tokens with this immediate parent coalesce.
            let mut occurrences = Vec::new();
            let mut in_error = false;
            for child in block.children_with_tokens() {
                let span =
                    usize::from(child.text_range().start())..usize::from(child.text_range().end());
                if child.kind() == Error {
                    assert!(child.as_token().is_some());
                    if in_error {
                        let (_, _, previous): &mut (_, _, Range<usize>) =
                            occurrences.last_mut().unwrap();
                        assert_eq!(previous.end, span.start);
                        previous.end = span.end;
                    } else {
                        occurrences.push((selected_role, RecoveryKind::Error, span));
                    }
                    in_error = true;
                } else {
                    in_error = false;
                    if child.kind() == Missing {
                        occurrences.push((selected_role, RecoveryKind::Missing, span));
                    }
                }
            }
            let expected_occurrences = if missing {
                vec![(selected_role, RecoveryKind::Missing, 10..10)]
            } else if error {
                vec![(selected_role, RecoveryKind::Error, 10..13)]
            } else {
                vec![]
            };
            assert_eq!(occurrences, expected_occurrences);

            let assert_eof = |exit, rest: &str| {
                assert_eq!(rest, "");
                let NormalizedExit::Complete(Err(Either::Right(mut eof)), line) = exit else {
                    panic!("expected ordinary EOF: {source:?}")
                };
                assert_eq!(line, LineEntry::InLine);
                assert!(eof.item.payload_view().is_eof());
                let end = origin + end;
                let extent = eof.item.extent(end);
                assert_eq!(extent.remaining(), end..end);
                assert_eq!(extent.payload(), end..end);
                assert_eq!(extent.recovery_range(), end..end);
                assert_eq!(emit_pending_leading_text(&mut eof.item), "");
            };
            assert_eof(exit, rest);
            // Temporary fresh/frozen records are a separate compatibility check;
            // only their absolute coordinates shift, not Rowan's local ranges.
            let expected_records = expected_occurrences
                .into_iter()
                .map(|(role, kind, span)| {
                    record(role, kind, origin + span.start..origin + span.end)
                })
                .collect::<Vec<_>>();
            assert_eq!(records, expected_records);
            let (again, frozen, again_exit, again_rest) =
                parse(source, 0, origin, None, Some(&records));
            assert_eq!(again, green);
            assert_eq!(frozen, records);
            assert_eof(again_exit, again_rest);
        }
    }
}

#[test]
fn indented_act_rowan_schema_covers_first_statement_missing_error_retry_and_control() {
    use SyntaxKind::*;

    let assert_children = |parent: &SyntaxNode, expected: &[(SyntaxKind, bool, Range<usize>)]| {
        let children = parent.children_with_tokens().collect::<Vec<_>>();
        assert_eq!(children.len(), expected.len());
        for (child, (kind, is_node, span)) in children.iter().zip(expected) {
            assert_eq!(child.kind(), *kind);
            assert_eq!(child.as_node().is_some(), *is_node);
            assert_eq!(child.parent(), Some(parent.clone()));
            assert_eq!(
                usize::from(child.text_range().start())..usize::from(child.text_range().end()),
                *span
            );
        }
    };

    for origin in [0, 41] {
        for (source, missing, error, statement_start) in [
            ("act A:\n  ", true, false, None),
            ("act A:\n  @ @", false, true, None),
            ("act A:\n  @ @ value", false, true, Some(12)),
            ("act A:\n  value", false, false, Some(9)),
        ] {
            let end = source.len();
            let (green, records, exit, rest) = parse(source, 0, origin, None, None);
            assert_eq!(green.to_string(), source);
            let root = SyntaxNode::new_root(green.clone());
            assert_eq!(root.kind(), Root);
            assert_eq!(range(&root), 0..end);
            assert_eq!(root.parent(), None);
            assert_children(&root, &[(Statement, true, 0..end)]);
            let statement = root.first_child().unwrap();
            assert_children(&statement, &[(ActDeclaration, true, 0..end)]);
            let declaration = statement.first_child().unwrap();
            assert_children(
                &declaration,
                &[
                    (ActKw, false, 0..3),
                    (Whitespace, false, 3..4),
                    (TypeExpression, true, 4..5),
                    (Colon, false, 5..6),
                    (IndentedStatementBlock, true, 6..end),
                ],
            );
            let head = declaration.first_child().unwrap();
            assert_eq!(head.to_string(), "A");
            let block = declaration.last_child().unwrap();
            // Completed direct Head, actual Colon and this Act-owned block
            // select the first Statement slot independently of recovery records.
            let selected_role = GrammarRole::Declaration(DeclarationRole::Act(
                ActDeclarationRole::IndentedStatement,
            ));
            let mut expected = vec![(Newline, false, 6..7), (Whitespace, false, 7..9)];
            if missing {
                expected.push((Missing, true, 9..9));
            }
            if error {
                expected.extend([
                    (Error, false, 9..10),
                    (Error, false, 10..11),
                    (Error, false, 11..12),
                ]);
            }
            if let Some(start) = statement_start {
                expected.push((Statement, true, start..end));
            }
            assert_children(&block, &expected);
            if let Some(start) = statement_start {
                let admitted = block.last_child().unwrap();
                assert_children(&admitted, &[(OperatorChain, true, start..end)]);
                let chain = admitted.first_child().unwrap();
                assert_children(&chain, &[(IdentifierExpression, true, start..end)]);
                let expression = chain.first_child().unwrap();
                if error {
                    assert_children(
                        &expression,
                        &[(Whitespace, false, 12..13), (Identifier, false, 13..18)],
                    );
                } else {
                    assert_children(&expression, &[(Identifier, false, 9..14)]);
                }
            }
            for element in root.descendants_with_tokens() {
                let span = usize::from(element.text_range().start())
                    ..usize::from(element.text_range().end());
                assert_eq!(element.to_string(), source[span]);
                assert_ne!(element.kind(), Invalid);
                if element.kind() == Missing {
                    let node = element.as_node().expect("empty Missing node");
                    assert_eq!(node.parent(), Some(block.clone()));
                    assert_eq!(node.children_with_tokens().count(), 0);
                }
            }
            for (kind, count) in [
                (Missing, usize::from(missing)),
                (Error, if error { 3 } else { 0 }),
            ] {
                assert_eq!(
                    root.descendants_with_tokens()
                        .filter(|element| element.kind() == kind)
                        .count(),
                    count
                );
            }

            // Only adjacent Error tokens with this immediate parent coalesce.
            let mut occurrences = Vec::new();
            let mut in_error = false;
            for child in block.children_with_tokens() {
                let span =
                    usize::from(child.text_range().start())..usize::from(child.text_range().end());
                if child.kind() == Error {
                    assert!(child.as_token().is_some());
                    if in_error {
                        let (_, _, previous): &mut (_, _, Range<usize>) =
                            occurrences.last_mut().unwrap();
                        assert_eq!(previous.end, span.start);
                        previous.end = span.end;
                    } else {
                        occurrences.push((selected_role, RecoveryKind::Error, span));
                    }
                    in_error = true;
                } else {
                    in_error = false;
                    if child.kind() == Missing {
                        occurrences.push((selected_role, RecoveryKind::Missing, span));
                    }
                }
            }
            let expected_occurrences = if missing {
                vec![(selected_role, RecoveryKind::Missing, 9..9)]
            } else if error {
                vec![(selected_role, RecoveryKind::Error, 9..12)]
            } else {
                vec![]
            };
            assert_eq!(occurrences, expected_occurrences);

            let assert_eof = |exit, rest: &str| {
                assert_eq!(rest, "");
                let NormalizedExit::Complete(Err(Either::Right(mut eof)), line) = exit else {
                    panic!("expected ordinary EOF: {source:?}")
                };
                assert_eq!(line, LineEntry::InLine);
                assert!(eof.item.payload_view().is_eof());
                let end = origin + end;
                let extent = eof.item.extent(end);
                assert_eq!(extent.remaining(), end..end);
                assert_eq!(extent.payload(), end..end);
                assert_eq!(extent.recovery_range(), end..end);
                assert_eq!(emit_pending_leading_text(&mut eof.item), "");
            };
            assert_eof(exit, rest);
            // Temporary fresh/frozen records are a separate compatibility check;
            // only their absolute coordinates shift, not Rowan's local ranges.
            let expected_records = expected_occurrences
                .into_iter()
                .map(|(role, kind, span)| {
                    record(role, kind, origin + span.start..origin + span.end)
                })
                .collect::<Vec<_>>();
            assert_eq!(records, expected_records);
            let (again, frozen, again_exit, again_rest) =
                parse(source, 0, origin, None, Some(&records));
            assert_eq!(again, green);
            assert_eq!(frozen, records);
            assert_eof(again_exit, again_rest);
        }
    }
}

#[test]
fn indented_impl_rowan_schema_covers_first_statement_missing_error_retry_and_control() {
    use SyntaxKind::*;

    let assert_children = |parent: &SyntaxNode, expected: &[(SyntaxKind, bool, Range<usize>)]| {
        let children = parent.children_with_tokens().collect::<Vec<_>>();
        assert_eq!(children.len(), expected.len());
        for (child, (kind, is_node, span)) in children.iter().zip(expected) {
            assert_eq!(child.kind(), *kind);
            assert_eq!(child.as_node().is_some(), *is_node);
            assert_eq!(child.parent(), Some(parent.clone()));
            assert_eq!(
                usize::from(child.text_range().start())..usize::from(child.text_range().end()),
                *span
            );
        }
    };

    for origin in [0, 41] {
        for (source, missing, error, statement_start) in [
            ("impl T: D:\n  ", true, false, None),
            ("impl T: D:\n  @ @", false, true, None),
            ("impl T: D:\n  @ @ value", false, true, Some(16)),
            ("impl T: D:\n  value", false, false, Some(13)),
        ] {
            let end = source.len();
            let (green, records, exit, rest) = parse(source, 0, origin, None, None);
            assert_eq!(green.to_string(), source);
            let root = SyntaxNode::new_root(green.clone());
            assert_eq!(root.kind(), Root);
            assert_eq!(range(&root), 0..end);
            assert_eq!(root.parent(), None);
            assert_children(&root, &[(Statement, true, 0..end)]);
            let statement = root.first_child().unwrap();
            assert_children(&statement, &[(ImplDeclaration, true, 0..end)]);
            let declaration = statement.first_child().unwrap();
            assert_children(
                &declaration,
                &[
                    (ImplKw, false, 0..4),
                    (Whitespace, false, 4..5),
                    (TypeExpression, true, 5..6),
                    (ImplDescription, true, 6..9),
                    (Colon, false, 9..10),
                    (IndentedStatementBlock, true, 10..end),
                ],
            );
            let head = declaration.first_child().unwrap();
            assert_eq!(head.to_string(), "T");
            let description = declaration.children().nth(1).unwrap();
            assert_children(
                &description,
                &[
                    (Colon, false, 6..7),
                    (Whitespace, false, 7..8),
                    (TypeExpression, true, 8..9),
                ],
            );
            assert_eq!(description.first_child().unwrap().to_string(), "D");
            let block = declaration.last_child().unwrap();
            // Completed Head and ImplDescription, then the direct second Colon and
            // Impl-owned block select this slot independently of recovery records.
            let selected_role =
                GrammarRole::Declaration(DeclarationRole::Impl(ImplRole::IndentedStatement));
            let mut expected = vec![(Newline, false, 10..11), (Whitespace, false, 11..13)];
            if missing {
                expected.push((Missing, true, 13..13));
            }
            if error {
                expected.extend([
                    (Error, false, 13..14),
                    (Error, false, 14..15),
                    (Error, false, 15..16),
                ]);
            }
            if let Some(start) = statement_start {
                expected.push((Statement, true, start..end));
            }
            assert_children(&block, &expected);
            if let Some(start) = statement_start {
                let admitted = block.last_child().unwrap();
                assert_children(&admitted, &[(OperatorChain, true, start..end)]);
                let chain = admitted.first_child().unwrap();
                assert_children(&chain, &[(IdentifierExpression, true, start..end)]);
                let expression = chain.first_child().unwrap();
                if error {
                    assert_children(
                        &expression,
                        &[(Whitespace, false, 16..17), (Identifier, false, 17..22)],
                    );
                } else {
                    assert_children(&expression, &[(Identifier, false, 13..18)]);
                }
            }
            for element in root.descendants_with_tokens() {
                let span = usize::from(element.text_range().start())
                    ..usize::from(element.text_range().end());
                assert_eq!(element.to_string(), source[span]);
                assert_ne!(element.kind(), Invalid);
                if element.kind() == Missing {
                    let node = element.as_node().expect("empty Missing node");
                    assert_eq!(node.parent(), Some(block.clone()));
                    assert_eq!(node.children_with_tokens().count(), 0);
                }
            }
            for (kind, count) in [
                (Missing, usize::from(missing)),
                (Error, if error { 3 } else { 0 }),
            ] {
                assert_eq!(
                    root.descendants_with_tokens()
                        .filter(|element| element.kind() == kind)
                        .count(),
                    count
                );
            }

            // Only adjacent Error tokens with this immediate parent coalesce.
            let mut occurrences = Vec::new();
            let mut in_error = false;
            for child in block.children_with_tokens() {
                let span =
                    usize::from(child.text_range().start())..usize::from(child.text_range().end());
                if child.kind() == Error {
                    assert!(child.as_token().is_some());
                    if in_error {
                        let (_, _, previous): &mut (_, _, Range<usize>) =
                            occurrences.last_mut().unwrap();
                        assert_eq!(previous.end, span.start);
                        previous.end = span.end;
                    } else {
                        occurrences.push((selected_role, RecoveryKind::Error, span));
                    }
                    in_error = true;
                } else {
                    in_error = false;
                    if child.kind() == Missing {
                        occurrences.push((selected_role, RecoveryKind::Missing, span));
                    }
                }
            }
            let expected_occurrences = if missing {
                vec![(selected_role, RecoveryKind::Missing, 13..13)]
            } else if error {
                vec![(selected_role, RecoveryKind::Error, 13..16)]
            } else {
                vec![]
            };
            assert_eq!(occurrences, expected_occurrences);

            let assert_eof = |exit, rest: &str| {
                assert_eq!(rest, "");
                let NormalizedExit::Complete(Err(Either::Right(mut eof)), line) = exit else {
                    panic!("expected ordinary EOF: {source:?}")
                };
                assert_eq!(line, LineEntry::InLine);
                assert!(eof.item.payload_view().is_eof());
                let end = origin + end;
                let extent = eof.item.extent(end);
                assert_eq!(extent.remaining(), end..end);
                assert_eq!(extent.payload(), end..end);
                assert_eq!(extent.recovery_range(), end..end);
                assert_eq!(emit_pending_leading_text(&mut eof.item), "");
            };
            assert_eof(exit, rest);
            // Temporary fresh/frozen records are a separate compatibility check;
            // only their absolute coordinates shift, not Rowan's local ranges.
            let expected_records = expected_occurrences
                .into_iter()
                .map(|(role, kind, span)| {
                    record(role, kind, origin + span.start..origin + span.end)
                })
                .collect::<Vec<_>>();
            assert_eq!(records, expected_records);
            let (again, frozen, again_exit, again_rest) =
                parse(source, 0, origin, None, Some(&records));
            assert_eq!(again, green);
            assert_eq!(frozen, records);
            assert_eof(again_exit, again_rest);
        }
    }
}

#[test]
fn indented_cast_rowan_schema_covers_first_statement_missing_error_retry_and_control() {
    use SyntaxKind::*;

    let assert_children = |parent: &SyntaxNode, expected: &[(SyntaxKind, bool, Range<usize>)]| {
        let children = parent.children_with_tokens().collect::<Vec<_>>();
        assert_eq!(children.len(), expected.len());
        for (child, (kind, is_node, span)) in children.iter().zip(expected) {
            assert_eq!(child.kind(), *kind);
            assert_eq!(child.as_node().is_some(), *is_node);
            assert_eq!(child.parent(), Some(parent.clone()));
            assert_eq!(
                usize::from(child.text_range().start())..usize::from(child.text_range().end()),
                *span
            );
        }
    };

    for origin in [0, 41] {
        for (source, missing, error, statement_start) in [
            ("cast(x): A =\n  ", true, false, None),
            ("cast(x): A =\n  @ @", false, true, None),
            ("cast(x): A =\n  @ @ value", false, true, Some(18)),
            ("cast(x): A =\n  value", false, false, Some(15)),
        ] {
            let end = source.len();
            let (green, records, exit, rest) = parse(source, 0, origin, None, None);
            assert_eq!(green.to_string(), source);
            let root = SyntaxNode::new_root(green.clone());
            assert_eq!(root.kind(), Root);
            assert_eq!(range(&root), 0..end);
            assert_eq!(root.parent(), None);
            assert_children(&root, &[(Statement, true, 0..end)]);
            let statement = root.first_child().unwrap();
            assert_children(&statement, &[(CastDeclaration, true, 0..end)]);
            let declaration = statement.first_child().unwrap();
            assert_children(
                &declaration,
                &[
                    (CastKw, false, 0..4),
                    (CastPattern, true, 4..7),
                    (CastTarget, true, 7..10),
                    (Whitespace, false, 10..11),
                    (Equals, false, 11..12),
                    (CastBody, true, 12..end),
                ],
            );
            let pattern = declaration.first_child().unwrap();
            assert_children(
                &pattern,
                &[
                    (LParen, false, 4..5),
                    (Pattern, true, 5..6),
                    (RParen, false, 6..7),
                ],
            );
            assert_eq!(pattern.first_child().unwrap().to_string(), "x");
            let target = declaration.children().nth(1).unwrap();
            assert_children(
                &target,
                &[
                    (Colon, false, 7..8),
                    (Whitespace, false, 8..9),
                    (TypeExpression, true, 9..10),
                ],
            );
            assert_eq!(target.first_child().unwrap().to_string(), "A");
            let body = declaration.last_child().unwrap();
            assert_children(&body, &[(IndentedStatementBlock, true, 12..end)]);
            let block = body.first_child().unwrap();
            // Completed Pattern/Target and actual Equals, followed by CastBody's
            // indented block, select this slot independently of recovery records.
            let selected_role =
                GrammarRole::Declaration(DeclarationRole::Cast(CastRole::IndentedStatement));
            let mut expected = vec![(Newline, false, 12..13), (Whitespace, false, 13..15)];
            if missing {
                expected.push((Missing, true, 15..15));
            }
            if error {
                expected.extend([
                    (Error, false, 15..16),
                    (Error, false, 16..17),
                    (Error, false, 17..18),
                ]);
            }
            if let Some(start) = statement_start {
                expected.push((Statement, true, start..end));
            }
            assert_children(&block, &expected);
            if let Some(start) = statement_start {
                let admitted = block.last_child().unwrap();
                assert_children(&admitted, &[(OperatorChain, true, start..end)]);
                let chain = admitted.first_child().unwrap();
                assert_children(&chain, &[(IdentifierExpression, true, start..end)]);
                let expression = chain.first_child().unwrap();
                if error {
                    assert_children(
                        &expression,
                        &[(Whitespace, false, 18..19), (Identifier, false, 19..24)],
                    );
                } else {
                    assert_children(&expression, &[(Identifier, false, 15..20)]);
                }
            }
            for element in root.descendants_with_tokens() {
                let span = usize::from(element.text_range().start())
                    ..usize::from(element.text_range().end());
                assert_eq!(element.to_string(), source[span]);
                assert_ne!(element.kind(), Invalid);
                if element.kind() == Missing {
                    let node = element.as_node().expect("empty Missing node");
                    assert_eq!(node.parent(), Some(block.clone()));
                    assert_eq!(node.children_with_tokens().count(), 0);
                }
            }
            for (kind, count) in [
                (Missing, usize::from(missing)),
                (Error, if error { 3 } else { 0 }),
            ] {
                assert_eq!(
                    root.descendants_with_tokens()
                        .filter(|element| element.kind() == kind)
                        .count(),
                    count
                );
            }

            // Only adjacent Error tokens with this immediate parent coalesce.
            let mut occurrences = Vec::new();
            let mut in_error = false;
            for child in block.children_with_tokens() {
                let span =
                    usize::from(child.text_range().start())..usize::from(child.text_range().end());
                if child.kind() == Error {
                    assert!(child.as_token().is_some());
                    if in_error {
                        let (_, _, previous): &mut (_, _, Range<usize>) =
                            occurrences.last_mut().unwrap();
                        assert_eq!(previous.end, span.start);
                        previous.end = span.end;
                    } else {
                        occurrences.push((selected_role, RecoveryKind::Error, span));
                    }
                    in_error = true;
                } else {
                    in_error = false;
                    if child.kind() == Missing {
                        occurrences.push((selected_role, RecoveryKind::Missing, span));
                    }
                }
            }
            let expected_occurrences = if missing {
                vec![(selected_role, RecoveryKind::Missing, 15..15)]
            } else if error {
                vec![(selected_role, RecoveryKind::Error, 15..18)]
            } else {
                vec![]
            };
            assert_eq!(occurrences, expected_occurrences);

            let assert_eof = |exit, rest: &str| {
                assert_eq!(rest, "");
                let NormalizedExit::Complete(Err(Either::Right(mut eof)), line) = exit else {
                    panic!("expected ordinary EOF: {source:?}")
                };
                assert_eq!(line, LineEntry::InLine);
                assert!(eof.item.payload_view().is_eof());
                let end = origin + end;
                let extent = eof.item.extent(end);
                assert_eq!(extent.remaining(), end..end);
                assert_eq!(extent.payload(), end..end);
                assert_eq!(extent.recovery_range(), end..end);
                assert_eq!(emit_pending_leading_text(&mut eof.item), "");
            };
            assert_eof(exit, rest);
            // Temporary fresh/frozen records are a separate compatibility check;
            // only their absolute coordinates shift, not Rowan's local ranges.
            let expected_records = expected_occurrences
                .into_iter()
                .map(|(role, kind, span)| {
                    record(role, kind, origin + span.start..origin + span.end)
                })
                .collect::<Vec<_>>();
            assert_eq!(records, expected_records);
            let (again, frozen, again_exit, again_rest) =
                parse(source, 0, origin, None, Some(&records));
            assert_eq!(again, green);
            assert_eq!(frozen, records);
            assert_eof(again_exit, again_rest);
        }
    }
}

#[test]
fn indented_colon_rowan_schema_uses_utf8_crlf_byte_ranges() {
    let (green, _, _, _) = parse("f:\r\n  💥", 0, 0, None, None);
    let block = colon_indented_block(&SyntaxNode::new_root(green));
    assert!(
        block
            .children_with_tokens()
            .filter(|element| element.kind() == SyntaxKind::Error)
            .all(|element| element.as_token().is_some())
    );
    assert_eq!(range(&block), 2..10);
    assert_eq!(
        direct_elements(&block),
        [
            (SyntaxKind::Newline, 2..4),
            (SyntaxKind::Whitespace, 4..6),
            (SyntaxKind::Error, 6..10),
        ]
    );
}

#[test]
fn indented_quoted_fence_and_utf8_crlf_use_physical_shifted_extents() {
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
    let role = GrammarRole::ColonApplication(ColonApplicationRole::IndentedStatement);
    for (source, expected, emitted) in [
        (
            "\r\n> > ```\nouter",
            record(role, RecoveryKind::Missing, 102..102),
            "",
        ),
        (
            "\r\n> >   💥\r\n> > ```\nouter",
            record(role, RecoveryKind::Error, 108..112),
            "\r\n> >   💥",
        ),
    ] {
        let mut frozen_records = None;
        for _ in 0..2 {
            let operators = OperatorTable::empty();
            let mut input = source;
            let mut recover = Recover::new_for_test(&operators);
            let mut output = frozen_records
                .as_deref()
                .map(|records| {
                    recover = Recover::reconcile_for_test(recover.operators(), records);
                    GreenNodeBuilder::new()
                })
                .unwrap_or_else(GreenNodeBuilder::new);
            output.start_node(SyntaxKind::Root.into());
            let exit = crate::statement::indented_statement_block_normalized(
                crate::cursor::SyntaxIn::new(&mut input, &mut recover, &mut output),
                0,
                role,
                STOP_ELSE,
                100,
                LineEntry::InLine,
                Some(&fence),
                Some(AmbientClaimView::root_statement(0)).into(),
            );
            output.finish_node();
            let (green, records) = (output.finish(), recover.finish_recoveries_for_test());
            assert_eq!(records, [expected.clone()], "{source:?}");
            assert_eq!(green.to_string(), emitted);
            assert_eq!(input, "> > ```\nouter");
            let NormalizedExit::Complete(Err(Either::Left(item)), LineEntry::PhysicalStart) = exit
            else {
                panic!("abstract boundary handoff")
            };
            assert_eq!(
                item.payload_view().pending_boundary().unwrap().coordinate(),
                100 + source.len() - input.len()
            );
            frozen_records = Some(records);
        }
    }
}
