use super::*;
use crate::{
    rewrite::{ambient_claim::AmbientClaimView, driver::MlMode, statement::StatementLineHandoff},
    session::{
        CaseLikeRole, DiagnosticId, ExpectationSources, ExpectedSyntax, ExpressionRole,
        ForStatementRole, GrammarRole, IfExpressionRole, RecoveryKind, RecoverySiteKey,
        SyntaxExpectation, UnexpectedCategory, UnexpectedSyntax,
    },
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
    let mut recover = Recover::new(&operators);
    let mut output = match frozen {
        Some(frozen) => GreenNodeBuilder::reconcile(frozen),
        None => GreenNodeBuilder::new(),
    };
    output.start_node(SyntaxKind::Root.into());
    output.start_node(SyntaxKind::OperatorChain.into());
    let (item, origin, line) = crate::rewrite::driver::expression_item(
        In::new(&mut input, &mut recover, &mut output),
        OperatorSite::Nud,
        0,
        LineEntry::InLine,
        None,
        0,
        stops,
    );
    let exit = crate::rewrite::driver::required_expr_item_normalized(
        In::new(&mut input, &mut recover, &mut output),
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
    );
    output.finish_node();
    output.finish_node();
    let (green, records) = output.finish_with_recoveries();
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
            expected: ExpectedSyntax::Expression,
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
    let mut recover = Recover::new(operators);
    let mut output = GreenNodeBuilder::new();
    output.start_node(SyntaxKind::Root.into());
    let mut exit = expr_normalized(
        In::new(&mut input, &mut recover, &mut output),
        None,
        0,
        0,
        MlMode::All,
        StatementLineHandoff::OrdinaryLayout,
        0,
        LineEntry::InLine,
        None,
        Some(AmbientClaimView::root_statement(0)).into(),
    );
    if let Some(NormalizedExit::Complete(Err(Either::Right(end)), _)) = &mut exit {
        emit_end(&mut output, end);
    }
    output.finish_node();
    let (green, records) = output.finish_with_recoveries();
    (green, exit, records)
}

fn statement_with_recoveries(
    source: &str,
) -> (GreenNode, NormalizedExit, Vec<CommittedRecoveryRecord>) {
    let operators = OperatorTable::empty();
    let mut input = source;
    let mut recover = Recover::new(&operators);
    let mut output = GreenNodeBuilder::new();
    output.start_node(SyntaxKind::Root.into());
    let mut exit = crate::rewrite::statement::statement_normalized(
        In::new(&mut input, &mut recover, &mut output),
        0,
        0,
        0,
        LineEntry::InLine,
        None,
        Some(AmbientClaimView::root_statement(0)).into(),
    );
    if let NormalizedExit::Complete(Err(Either::Right(end)), _) = &mut exit {
        emit_end(&mut output, end);
    }
    output.finish_node();
    let (green, records) = output.finish_with_recoveries();
    (green, exit, records)
}

#[test]
fn required_operand_unclaimed_close_publishes_missing_and_keeps_its_whole_item() {
    let operators = OperatorTable::from_declarations([OperatorDeclaration::new(
        "?",
        OperatorFixities::new().with_prefix(BindingPower::scalar(70)),
    )])
    .unwrap();
    let mut recover = Recover::new(&operators);
    let mut input = "? ]";
    let mut output = GreenNodeBuilder::new();
    output.start_node(SyntaxKind::Root.into());
    let rejected = expr_normalized(
        In::new(&mut input, &mut recover, &mut output),
        None,
        0,
        0,
        MlMode::All,
        StatementLineHandoff::OrdinaryLayout,
        0,
        LineEntry::InLine,
        None,
        Some(AmbientClaimView::root_statement(0)).into(),
    );
    assert!(rejected.is_none());
    assert_eq!(input, "? ]");
    assert_eq!(output.recovery_slot_count(), 0);

    let mut input = " ]";
    output.start_node(SyntaxKind::OperatorChain.into());
    let (item, origin, line) = crate::rewrite::driver::expression_item(
        In::new(&mut input, &mut recover, &mut output),
        OperatorSite::Nud,
        0,
        LineEntry::InLine,
        None,
        0,
        0,
    );
    let exit = crate::rewrite::driver::required_expr_item_normalized(
        In::new(&mut input, &mut recover, &mut output),
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
    );
    output.finish_node();
    output.finish_node();
    let (green, records) = output.finish_with_recoveries();
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
        (",", super::super::operator::STOP_COMMA, "", 0..0),
        ("]", 0, "", 0..0),
        ("[", 0, "", 0..0),
        ("\r\n", super::super::operator::STOP_LINE_BREAK, "", 0..0),
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
    assert!(
        SyntaxNode::new_root(green.clone())
            .descendants()
            .any(|node| node.kind() == SyntaxKind::Error)
    );

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
        direct_required_expr_with_recoveries("@ ,", role, super::super::operator::STOP_COMMA, None);
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
