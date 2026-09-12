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
