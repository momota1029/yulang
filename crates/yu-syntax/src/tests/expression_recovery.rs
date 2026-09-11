use crate::tests::support::*;
use crate::{
    ambient_claim::AmbientClaimView,
    handoff::MlMode,
    recovery_record::{
        CaseLikeRole, DiagnosticId, ExpectationSources, ExpectedSyntax, ExpressionRole,
        ForStatementRole, GrammarRole, IfExpressionRole, RecoveryKind, RecoverySiteKey,
        SyntaxExpectation, UnexpectedCategory, UnexpectedSyntax,
    },
    statement::StatementLineHandoff,
};
use std::sync::Arc;

fn direct_required_expr_with_recoveries<'source, 'frozen>(
    source: &'source str,
    role: GrammarRole,
    stops: Stops,
    frozen: Option<&'frozen [CommittedRecoveryRecord]>,
) -> (
    GreenNode,
    NormalizedExit,
    &'source str,
    Vec<CommittedRecoveryRecord>,
) {
    let operators = OperatorTable::empty();
    let mut input = source;
    let mut recover = Recover::new_for_test(&operators);
    let mut output = match frozen {
        Some(frozen) => {
            recover = Recover::reconcile_for_test(recover.operators(), frozen);
            GreenNodeBuilder::new()
        }
        None => GreenNodeBuilder::new(),
    };
    output.start_node(SyntaxKind::Root.into());
    output.start_node(SyntaxKind::OperatorChain.into());
    let (item, origin, line) = crate::lexical::expression_item::expression_item(
        crate::cursor::SyntaxIn::new(&mut input, &mut recover, &mut output),
        OperatorSite::Nud,
        0,
        LineEntry::InLine,
        None,
        0,
        stops,
    );
    let exit = crate::expression::required_expr_item_normalized(
        crate::cursor::SyntaxIn::new(&mut input, &mut recover, &mut output),
        item,
        role,
        None,
        0,
        stops,
        MlMode::All,
        StatementLineHandoff::OrdinaryLayout,
        origin,
        line,
        None,
        Some(AmbientClaimView::root_statement(0)).into(),
        None,
    );
    output.finish_node();
    output.finish_node();
    let (green, records) = (output.finish(), recover.finish_recoveries_for_test());
    (green, exit, input, records)
}

fn assert_expression_record(
    record: &CommittedRecoveryRecord,
    role: GrammarRole,
    kind: RecoveryKind,
    range: std::ops::Range<usize>,
) {
    assert_eq!(
        record.site,
        RecoverySiteKey {
            role,
            range: range.clone()
        }
    );
    assert_eq!(record.kind, kind);
    assert_eq!(
        record.expectations,
        Arc::from([SyntaxExpectation {
            role,
            expected: match role {
                GrammarRole::ForStatement(ForStatementRole::Body) => ExpectedSyntax::Statement,
                _ => ExpectedSyntax::Expression,
            },
            range: range.clone(),
            sources: ExpectationSources::COMMITTED_RECOVERY_RULE,
        }]),
    );
    assert_eq!(record.primary_expectation, 0);
    assert_eq!(
        record.unexpected,
        match kind {
            RecoveryKind::Missing => Arc::from([]),
            RecoveryKind::Error => Arc::from([UnexpectedSyntax::Token {
                range,
                category: UnexpectedCategory::OtherCharacter,
            }]),
        },
    );
}

fn expression_with_recoveries(
    source: &str,
    operators: &OperatorTable,
) -> (
    GreenNode,
    Option<NormalizedExit>,
    Vec<CommittedRecoveryRecord>,
) {
    let mut input = source;
    let mut recover = Recover::new_for_test(operators);
    let mut output = GreenNodeBuilder::new();
    output.start_node(SyntaxKind::Root.into());
    let mut exit = expr_normalized(
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
        None,
    );
    if let Some(NormalizedExit::Complete(Err(Either::Right(end)), _)) = &mut exit {
        emit_end(&mut output, end);
    }
    output.finish_node();
    let (green, records) = (output.finish(), recover.finish_recoveries_for_test());
    (green, exit, records)
}

fn statement_with_recoveries(
    source: &str,
) -> (GreenNode, NormalizedExit, Vec<CommittedRecoveryRecord>) {
    statement_with_frozen_recoveries(source, None)
}

fn statement_with_frozen_recoveries(
    source: &str,
    frozen: Option<&[CommittedRecoveryRecord]>,
) -> (GreenNode, NormalizedExit, Vec<CommittedRecoveryRecord>) {
    let operators = OperatorTable::empty();
    let mut input = source;
    let mut recover = Recover::new_for_test(&operators);
    let mut output = match frozen {
        Some(frozen) => {
            recover = Recover::reconcile_for_test(recover.operators(), frozen);
            GreenNodeBuilder::new()
        }
        None => GreenNodeBuilder::new(),
    };
    output.start_node(SyntaxKind::Root.into());
    let mut exit = crate::statement::statement_normalized(
        crate::cursor::SyntaxIn::new(&mut input, &mut recover, &mut output),
        0,
        0,
        0,
        LineEntry::InLine,
        None,
        Some(AmbientClaimView::root_statement(0)).into(),
        Some(crate::sequence::SequenceOwner::RootStatement),
    );
    if let NormalizedExit::Complete(Err(Either::Right(end)), _) = &mut exit {
        emit_end(&mut output, end);
    }
    output.finish_node();
    let (green, records) = (output.finish(), recover.finish_recoveries_for_test());
    (green, exit, records)
}

#[test]
fn required_operand_unclaimed_close_publishes_missing_and_keeps_its_whole_item() {
    let operators = OperatorTable::from_declarations([OperatorDeclaration::new(
        "?",
        OperatorFixities::new().with_prefix(BindingPower::scalar(70)),
    )])
    .unwrap();
    let mut recover = Recover::new_for_test(&operators);
    let mut input = "? ]";
    let mut output = GreenNodeBuilder::new();
    output.start_node(SyntaxKind::Root.into());
    let rejected = expr_normalized(
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
        None,
    );
    assert!(rejected.is_none());
    assert_eq!(input, "? ]");
    assert_eq!(recover.recovery_slot_count(), 0);

    let mut input = " ]";
    output.start_node(SyntaxKind::OperatorChain.into());
    let (item, origin, line) = crate::lexical::expression_item::expression_item(
        crate::cursor::SyntaxIn::new(&mut input, &mut recover, &mut output),
        OperatorSite::Nud,
        0,
        LineEntry::InLine,
        None,
        0,
        0,
    );
    let exit = crate::expression::required_expr_item_normalized(
        crate::cursor::SyntaxIn::new(&mut input, &mut recover, &mut output),
        item,
        GrammarRole::Expression(ExpressionRole::Nud),
        None,
        0,
        0,
        MlMode::All,
        StatementLineHandoff::OrdinaryLayout,
        origin,
        line,
        None,
        Some(AmbientClaimView::root_statement(0)).into(),
        None,
    );
    output.finish_node();
    output.finish_node();
    let (green, records) = (output.finish(), recover.finish_recoveries_for_test());
    assert_eq!(green.to_string(), "");
    let role = GrammarRole::Expression(ExpressionRole::Nud);
    assert_eq!(
        records,
        [CommittedRecoveryRecord {
            id: DiagnosticId(0),
            site: RecoverySiteKey { role, range: 0..0 },
            kind: RecoveryKind::Missing,
            unexpected: Arc::from([]),
            expectations: Arc::from([SyntaxExpectation {
                role,
                expected: ExpectedSyntax::Expression,
                range: 0..0,
                sources: ExpectationSources::COMMITTED_RECOVERY_RULE,
            }]),
            primary_expectation: 0,
        }]
    );
    let NormalizedExit::Complete(Err(Either::Left(item)), LineEntry::InLine) = exit else {
        panic!("the same bracket must remain pending")
    };
    assert_eq!(token_kind(&item), Some(TokenKind::RBracket));
    assert_eq!(item.extent(origin).recovery_range(), 0..2);
    assert_eq!(input, "");
}

#[test]
fn required_operand_boundaries_keep_items_except_ordinary_eof_leading() {
    let role = GrammarRole::Expression(ExpressionRole::Nud);
    for (source, stops, expected_green, range) in [
        ("", 0, "", 0..0),
        (" ", 0, " ", 1..1),
        (",", crate::lexical::stops::STOP_COMMA, "", 0..0),
        ("]", 0, "", 0..0),
        ("[", 0, "", 0..0),
        ("\r\n", crate::lexical::stops::STOP_LINE_BREAK, "", 0..0),
    ] {
        let (green, exit, remainder, records) =
            direct_required_expr_with_recoveries(source, role, stops, None);
        assert_eq!(green.to_string(), expected_green, "{source:?}");
        assert_eq!(records.len(), 1, "{source:?}");
        assert_expression_record(&records[0], role, RecoveryKind::Missing, range);
        assert!(
            matches!(exit, NormalizedExit::Complete(Err(_), _)),
            "{source:?}"
        );
        assert_eq!(remainder, "", "{source:?}");
    }
}

#[test]
fn required_operand_error_run_is_typed_retries_and_reconciles() {
    let role = GrammarRole::Expression(ExpressionRole::Nud);
    let (green, exit, remainder, fresh) =
        direct_required_expr_with_recoveries("@ x", role, 0, None);
    assert_eq!(green.to_string(), "@ x");
    assert!(matches!(
        exit,
        NormalizedExit::Complete(Err(Either::Right(_)), _)
    ));
    assert_eq!(remainder, "");
    assert_eq!(fresh.len(), 1);
    assert_expression_record(&fresh[0], role, RecoveryKind::Error, 0..1);
    let root = SyntaxNode::new_root(green.clone());
    let chain = root.first_child().unwrap();
    assert_eq!(chain.kind(), SyntaxKind::OperatorChain);
    let children = chain.children_with_tokens().collect::<Vec<_>>();
    assert_eq!(children[0].as_token().unwrap().kind(), SyntaxKind::Error);
    assert_eq!(children[0].to_string(), "@");
    assert_eq!(children[1].kind(), SyntaxKind::IdentifierExpression);
    assert_eq!(children[1].to_string(), " x");
    let retry = children[1]
        .as_node()
        .unwrap()
        .children_with_tokens()
        .collect::<Vec<_>>();
    assert_eq!(retry[0].kind(), SyntaxKind::Whitespace);
    assert_eq!(retry[0].to_string(), " ");
    assert_eq!(retry[1].kind(), SyntaxKind::Identifier);
    assert_eq!(retry[1].to_string(), "x");
    assert_eq!(retry.len(), 2);
    assert_eq!(children.len(), 2);

    let (frozen_green, frozen_exit, frozen_remainder, frozen) =
        direct_required_expr_with_recoveries("@ x", role, 0, Some(&fresh));
    assert_eq!(frozen_green, green);
    assert_eq!(frozen, fresh);
    assert_eq!(frozen_remainder, "");
    assert!(matches!(
        frozen_exit,
        NormalizedExit::Complete(Err(Either::Right(_)), _)
    ));

    let (_, boundary_exit, boundary_remainder, boundary_records) =
        direct_required_expr_with_recoveries("@ ,", role, crate::lexical::stops::STOP_COMMA, None);
    assert_eq!(boundary_records.len(), 1);
    assert_expression_record(&boundary_records[0], role, RecoveryKind::Error, 0..1);
    assert!(matches!(
        boundary_exit,
        NormalizedExit::Complete(Err(Either::Left(_)), _)
    ));
    assert_eq!(boundary_remainder, "");

    let operators = OperatorTable::from_declarations([OperatorDeclaration::new(
        "+",
        OperatorFixities::new().with_infix(BindingPower::scalar(50), BindingPower::scalar(50)),
    )])
    .unwrap();
    let (_, _, infix_records) = expression_with_recoveries("a + @ b", &operators);
    assert_eq!(infix_records.len(), 1);
    assert_expression_record(&infix_records[0], role, RecoveryKind::Error, 4..5);
}

#[test]
fn required_for_inline_body_missing_and_error_expect_statement_and_reconcile() {
    let role = GrammarRole::ForStatement(ForStatementRole::Body);
    for (source, kind, range) in [
        (" ]", RecoveryKind::Missing, 0..0),
        (" @", RecoveryKind::Error, 1..2),
    ] {
        let (green, _, remainder, records) =
            direct_required_expr_with_recoveries(source, role, 0, None);
        assert_eq!(records.len(), 1);
        assert_expression_record(&records[0], role, kind, range);
        assert_eq!(
            records[0].expectations[0].expected,
            ExpectedSyntax::Statement
        );
        let (reconciled_green, _, reconciled_remainder, reconciled) =
            direct_required_expr_with_recoveries(source, role, 0, Some(&records));
        assert_eq!(reconciled_green, green);
        assert_eq!(reconciled_remainder, remainder);
        assert_eq!(reconciled, records);
    }
}

#[test]
fn actual_for_inline_body_missing_and_error_expect_statement_and_reconcile() {
    let role = GrammarRole::ForStatement(ForStatementRole::Body);
    for (source, kind, range, emitted) in [
        (
            "for x in xs: ]",
            RecoveryKind::Missing,
            13..13,
            "for x in xs: ",
        ),
        (
            "for x in xs: @",
            RecoveryKind::Error,
            13..14,
            "for x in xs: @",
        ),
    ] {
        let (green, exit, records) = statement_with_frozen_recoveries(source, None);
        assert_eq!(green.to_string(), emitted);
        assert_eq!(records.len(), 1);
        assert_eq!(records[0].id, DiagnosticId(0));
        assert_expression_record(&records[0], role, kind, range.clone());
        assert_eq!(
            records[0].expectations[0].expected,
            ExpectedSyntax::Statement
        );
        let root = SyntaxNode::new_root(green.clone());
        let expected_body = match kind {
            RecoveryKind::Missing => "        Missing@13..13\n",
            RecoveryKind::Error => "        Error@13..14 \"@\"\n",
        };
        assert_eq!(
            format!("{root:#?}"),
            format!(
                concat!(
                    "Root@0..{end}\n",
                    "  Statement@0..{end}\n",
                    "    ForStatement@0..{end}\n",
                    "      ForKw@0..3 \"for\"\n",
                    "      Whitespace@3..4 \" \"\n",
                    "      Pattern@4..5\n",
                    "        IdentifierPattern@4..5\n",
                    "          Identifier@4..5 \"x\"\n",
                    "      Whitespace@5..6 \" \"\n",
                    "      InKw@6..8 \"in\"\n",
                    "      Whitespace@8..9 \" \"\n",
                    "      ForIterable@9..11\n",
                    "        OperatorChain@9..11\n",
                    "          IdentifierExpression@9..11\n",
                    "            Identifier@9..11 \"xs\"\n",
                    "      Colon@11..12 \":\"\n",
                    "      Whitespace@12..13 \" \"\n",
                    "      OperatorChain@13..{end}\n",
                    "{expected_body}",
                ),
                end = range.end,
                expected_body = expected_body,
            )
        );
        let recovery_kind = match kind {
            RecoveryKind::Missing => SyntaxKind::Missing,
            RecoveryKind::Error => SyntaxKind::Error,
        };
        let recovery_elements: Vec<_> = root
            .descendants_with_tokens()
            .filter(|node| matches!(node.kind(), SyntaxKind::Missing | SyntaxKind::Error))
            .collect();
        assert_eq!(recovery_elements.len(), 1);
        let recovery = &recovery_elements[0];
        assert_eq!(recovery.as_token().is_some(), kind == RecoveryKind::Error);
        assert_eq!(recovery.kind(), recovery_kind);
        assert_eq!(usize::from(recovery.text_range().start()), range.start);
        assert_eq!(usize::from(recovery.text_range().end()), range.end);
        let chain = recovery.parent().expect("inline body chain");
        assert_eq!(chain.kind(), SyntaxKind::OperatorChain);
        assert_eq!(chain.parent().unwrap().kind(), SyntaxKind::ForStatement);
        match kind {
            RecoveryKind::Missing => {
                let NormalizedExit::Complete(Err(Either::Left(item)), _) = &exit else {
                    panic!("the body close must remain pending")
                };
                assert_eq!(token_kind(item), Some(TokenKind::RBracket));
                assert_eq!(recovery.to_string(), "");
            }
            RecoveryKind::Error => {
                assert!(matches!(
                    exit,
                    NormalizedExit::Complete(Err(Either::Right(_)), _)
                ));
                assert_eq!(recovery.to_string(), "@");
            }
        }
        let (reconciled_green, reconciled_exit, reconciled) =
            statement_with_frozen_recoveries(source, Some(&records));
        assert_eq!(reconciled_green, green);
        for candidate in [&exit, &reconciled_exit] {
            let item = match candidate {
                NormalizedExit::Complete(Err(Either::Left(item)), LineEntry::InLine)
                    if kind == RecoveryKind::Missing =>
                {
                    item
                }
                NormalizedExit::Complete(Err(Either::Right(end)), LineEntry::InLine)
                    if kind == RecoveryKind::Error =>
                {
                    assert!(end.item.payload_view().is_eof());
                    &end.item
                }
                _ => panic!("fresh and frozen inline bodies must preserve the InLine handoff"),
            };
            let extent = item.extent(source.len());
            match kind {
                RecoveryKind::Missing => {
                    assert_eq!(extent.physical(), 12..14);
                    assert_eq!(extent.leading(), 12..13);
                    assert_eq!(extent.remaining(), 13..13);
                    assert_eq!(extent.payload(), 13..14);
                    assert_eq!(extent.recovery_range(), 13..14);
                }
                RecoveryKind::Error => {
                    assert_eq!(extent.physical(), 14..14);
                    assert_eq!(extent.leading(), 14..14);
                    assert_eq!(extent.remaining(), 14..14);
                    assert_eq!(extent.payload(), 14..14);
                    assert_eq!(extent.recovery_range(), 14..14);
                }
            }
        }
        match (exit, reconciled_exit) {
            (
                NormalizedExit::Complete(Err(Either::Left(item)), line),
                NormalizedExit::Complete(Err(Either::Left(reconciled_item)), reconciled_line),
            ) => {
                assert_eq!(token_kind(&reconciled_item), token_kind(&item));
                assert_eq!(reconciled_line, line);
            }
            (
                NormalizedExit::Complete(Err(Either::Right(_)), line),
                NormalizedExit::Complete(Err(Either::Right(_)), reconciled_line),
            ) => assert_eq!(reconciled_line, line),
            _ => panic!("reconciliation must preserve the body handoff"),
        }
        assert_eq!(reconciled, records);
    }
}

#[test]
fn required_operand_callers_publish_their_own_roles() {
    let operators = OperatorTable::empty();
    let (_, _, if_records) = expression_with_recoveries("if : x", &operators);
    assert!(if_records.iter().any(|record| {
        record.site.role == GrammarRole::IfExpression(IfExpressionRole::Condition)
            && record.kind == RecoveryKind::Missing
    }));

    let (_, _, case_records) = expression_with_recoveries("case : _ -> x", &operators);
    assert!(case_records.iter().any(|record| {
        record.site.role == GrammarRole::CaseLike(CaseLikeRole::Scrutinee)
            && record.kind == RecoveryKind::Missing
    }));
    let (_, _, guard_records) = expression_with_recoveries("case x: _ if -> y", &operators);
    assert!(guard_records.iter().any(|record| {
        record.site.role == GrammarRole::CaseLike(CaseLikeRole::Guard)
            && record.kind == RecoveryKind::Missing
    }));

    let (_, _, for_iterable_records) = statement_with_recoveries("for x in ]");
    assert_eq!(for_iterable_records.len(), 1);
    assert_expression_record(
        &for_iterable_records[0],
        GrammarRole::ForStatement(ForStatementRole::Iterable),
        RecoveryKind::Missing,
        9..9,
    );

    let (_, _, for_body_records) = statement_with_recoveries("for x in xs: @");
    assert_eq!(for_body_records.len(), 1);
    assert_expression_record(
        &for_body_records[0],
        GrammarRole::ForStatement(ForStatementRole::Body),
        RecoveryKind::Error,
        13..14,
    );
}

fn direct_child(node: &SyntaxNode, kind: SyntaxKind) -> SyntaxNode {
    node.children()
        .find(|child| child.kind() == kind)
        .unwrap_or_else(|| panic!("{kind:?} direct child of {:#?}", node.kind()))
}

fn direct_missing_in_required_chain(slot: &SyntaxNode) -> SyntaxNode {
    let chain = direct_child(slot, SyntaxKind::OperatorChain);
    let missing = direct_child(&chain, SyntaxKind::Missing);
    assert_eq!(missing.text_range(), chain.text_range());
    missing
}

#[test]
fn required_operand_cst_slots_select_initial_callers_without_recovery_records() {
    for (source, slot) in [
        ("if : x", SyntaxKind::Condition),
        ("case : _ -> x", SyntaxKind::CaseScrutinee),
        ("catch : _ -> x", SyntaxKind::CatchScrutinee),
        ("case x: _ if -> y", SyntaxKind::CaseGuard),
        ("catch x: _ if -> y", SyntaxKind::CatchGuard),
        ("for x in ]", SyntaxKind::ForIterable),
        ("for x in\n]", SyntaxKind::ForIterable),
    ] {
        let (green, _, _) = run_statement_normalized(source, 0, LineEntry::InLine, None);
        let root = SyntaxNode::new_root(green);
        let owner = root.descendants().find(|node| node.kind() == slot).unwrap();
        let missing = direct_missing_in_required_chain(&owner);
        assert_eq!(
            usize::from(missing.text_range().start()),
            owner.text_range().end().into()
        );
    }

    let (green, _, _) = run_statement_normalized(
        "for x in\r\n> > ```\nouter",
        0,
        LineEntry::InLine,
        Some(&FenceBoundary {
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
        }),
    );
    let root = SyntaxNode::new_root(green);
    let iterable = root
        .descendants()
        .find(|node| node.kind() == SyntaxKind::ForIterable)
        .unwrap();
    assert_eq!(
        direct_missing_in_required_chain(&iterable).text_range(),
        rowan::TextRange::new(8.into(), 8.into())
    );
}

#[test]
fn required_operand_cst_keeps_nested_nud_and_terminal_recovery_distinct() {
    let operators = OperatorTable::from_declarations([
        OperatorDeclaration::new(
            "?",
            OperatorFixities::new().with_prefix(BindingPower::scalar(70)),
        ),
        OperatorDeclaration::new(
            "+",
            OperatorFixities::new().with_infix(BindingPower::scalar(50), BindingPower::scalar(50)),
        ),
    ])
    .unwrap();
    for (source, operator) in [
        ("? @ x", SyntaxKind::PrefixOperatorUse),
        ("a + @ x", SyntaxKind::InfixOperatorUse),
    ] {
        let (green, _, _) = expression_with_recoveries(source, &operators);
        let root = SyntaxNode::new_root(green);
        let chain = direct_child(&root, SyntaxKind::OperatorChain);
        let children = chain.children_with_tokens().collect::<Vec<_>>();
        assert!(children.iter().any(|child| child.kind() == operator));
        let error = children
            .iter()
            .position(|child| child.kind() == SyntaxKind::Error)
            .unwrap();
        let retry = children
            .iter()
            .enumerate()
            .skip(error + 1)
            .find_map(|(index, child)| {
                (child.kind() == SyntaxKind::IdentifierExpression).then_some(index)
            })
            .unwrap();
        assert!(error < retry);
        let retry = children[retry].as_node().unwrap();
        assert_eq!(retry.parent().unwrap().kind(), SyntaxKind::OperatorChain);
    }

    for source in ["]", "@ x", "@\r\n界"] {
        let (green, _, _, _) = direct_required_expr_with_recoveries(
            source,
            GrammarRole::Expression(ExpressionRole::Nud),
            0,
            None,
        );
        let root = SyntaxNode::new_root(green);
        let chain = direct_child(&root, SyntaxKind::OperatorChain);
        if source == "]" {
            assert_eq!(
                direct_child(&chain, SyntaxKind::Missing).text_range(),
                rowan::TextRange::new(0.into(), 0.into())
            );
        } else {
            let elements = chain.children_with_tokens().collect::<Vec<_>>();
            let error = elements
                .iter()
                .find(|child| child.kind() == SyntaxKind::Error)
                .unwrap();
            assert_eq!(
                error.text_range(),
                rowan::TextRange::new(0.into(), 1.into())
            );
            assert!(
                elements
                    .iter()
                    .any(|child| child.kind() == SyntaxKind::IdentifierExpression)
            );
        }
    }
}

#[test]
fn required_operand_cst_orders_caller_and_nested_nud_recovery_in_one_chain() {
    let operators = OperatorTable::from_declarations([
        OperatorDeclaration::new(
            "?",
            OperatorFixities::new().with_prefix(BindingPower::scalar(70)),
        ),
        OperatorDeclaration::new(
            "+",
            OperatorFixities::new().with_infix(BindingPower::scalar(50), BindingPower::scalar(50)),
        ),
    ])
    .unwrap();
    for (source, accepted, nested_kind) in [
        (
            "if @ ? [: x",
            SyntaxKind::PrefixOperatorUse,
            SyntaxKind::Missing,
        ),
        (
            "if @ a + @ x: y",
            SyntaxKind::InfixOperatorUse,
            SyntaxKind::Error,
        ),
    ] {
        let (green, _, _) = expression_with_recoveries(source, &operators);
        let root = SyntaxNode::new_root(green);
        let condition = root
            .descendants()
            .find(|node| node.kind() == SyntaxKind::Condition)
            .unwrap();
        let chain = direct_child(&condition, SyntaxKind::OperatorChain);
        let elements = chain.children_with_tokens().collect::<Vec<_>>();
        let caller_error = elements
            .iter()
            .position(|child| child.kind() == SyntaxKind::Error)
            .unwrap();
        let accepted = elements
            .iter()
            .position(|child| child.kind() == accepted)
            .unwrap();
        let nested = elements
            .iter()
            .enumerate()
            .skip(accepted + 1)
            .find_map(|(index, child)| (child.kind() == nested_kind).then_some(index))
            .unwrap();
        assert!(caller_error < accepted && accepted < nested, "{source:?}");
        assert_eq!(
            elements
                .iter()
                .filter(|child| child.kind() == SyntaxKind::Missing)
                .count(),
            usize::from(nested_kind == SyntaxKind::Missing)
        );
    }

    let (green, _, _, _) = direct_required_expr_with_recoveries(
        "@",
        GrammarRole::Expression(ExpressionRole::Nud),
        0,
        None,
    );
    let root = SyntaxNode::new_root(green);
    let chain = direct_child(&root, SyntaxKind::OperatorChain);
    assert!(
        chain
            .children_with_tokens()
            .any(|child| child.kind() == SyntaxKind::Error)
    );
    assert!(
        !chain
            .children_with_tokens()
            .any(|child| child.kind() == SyntaxKind::Missing)
    );
}
