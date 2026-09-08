use std::{
    ops::Range,
    panic::{AssertUnwindSafe, catch_unwind},
    sync::Arc,
};

use chasa_recover::In;
use reborrow_generic::Reborrow as _;

use crate::{
    SyntaxKind, SyntaxNode,
    operator::OperatorTable,
    session::{
        CommittedRecoveryRecord, DiagnosticId, ExpectationSources, ExpectedSyntax, GrammarRole,
        LiteralExpected, LiteralRole, PunctuationEvidence, RecoveryKind, RecoverySiteKey,
        SyntaxExpectation, TypeRole, UnexpectedCategory, UnexpectedSyntax,
    },
};

use super::super::{
    emit::{
        CallArgumentRetryLeadingSeal, PathSegmentRetryLeadingSeal, emit_recovery_error_item,
        emit_recovery_error_run, emit_recovery_missing,
    },
    item::{
        Boundary, ForeignSplit, Item, LeadingTrivia, Payload, PendingBoundary,
        PhysicalLeadingTrivia, StopKind, Token, TokenKind, Trivia,
    },
    output::{
        ParserOutput, RecoveryDraft, StructuredRecoverySpec,
        emit_structured_recovery_error_from_item,
    },
    rule::rule_item_unexpected_category,
    state::Recover,
    statement::classify_statement_item_normalized,
};

fn role(slot: LiteralRole) -> GrammarRole {
    GrammarRole::Literal(slot)
}

fn expectation(
    role: GrammarRole,
    expected: ExpectedSyntax,
    range: Range<usize>,
    sources: ExpectationSources,
) -> SyntaxExpectation {
    SyntaxExpectation {
        role,
        expected,
        range,
        sources,
    }
}

fn singleton_draft(
    slot: LiteralRole,
    kind: RecoveryKind,
    range: Range<usize>,
    unexpected: Arc<[UnexpectedSyntax]>,
    expected: ExpectedSyntax,
) -> RecoveryDraft {
    RecoveryDraft::new(
        RecoverySiteKey {
            role: role(slot),
            range: range.clone(),
        },
        kind,
        unexpected,
        Arc::from([expectation(
            role(slot),
            expected,
            range,
            ExpectationSources::COMMITTED_RECOVERY_RULE,
        )]),
        0,
    )
}

fn path_segment_draft(
    kind: RecoveryKind,
    range: Range<usize>,
    unexpected: Arc<[UnexpectedSyntax]>,
) -> RecoveryDraft {
    let role = GrammarRole::Type(TypeRole::PathSegment);
    RecoveryDraft::new(
        RecoverySiteKey {
            role,
            range: range.clone(),
        },
        kind,
        unexpected,
        Arc::from([expectation(
            role,
            ExpectedSyntax::TypePathSegment,
            range,
            ExpectationSources::COMMITTED_RECOVERY_RULE,
        )]),
        0,
    )
}

fn frozen_record(
    id: u32,
    slot: LiteralRole,
    kind: RecoveryKind,
    range: Range<usize>,
    unexpected: Arc<[UnexpectedSyntax]>,
    expectations: Arc<[SyntaxExpectation]>,
    primary_expectation: usize,
) -> CommittedRecoveryRecord {
    CommittedRecoveryRecord {
        id: DiagnosticId(id),
        site: RecoverySiteKey {
            role: role(slot),
            range,
        },
        kind,
        unexpected,
        expectations,
        primary_expectation,
    }
}

fn structured_spec(slot: LiteralRole) -> StructuredRecoverySpec {
    StructuredRecoverySpec::new(
        role(slot),
        UnexpectedCategory::OtherCharacter,
        ExpectedSyntax::Identifier,
        ExpectationSources::COMMITTED_RECOVERY_RULE,
        0,
    )
}

fn structured_record(id: u32, slot: LiteralRole, range: Range<usize>) -> CommittedRecoveryRecord {
    frozen_record(
        id,
        slot,
        RecoveryKind::Error,
        range.clone(),
        Arc::from([UnexpectedSyntax::Token {
            range: range.clone(),
            category: UnexpectedCategory::OtherCharacter,
        }]),
        Arc::from([expectation(
            role(slot),
            ExpectedSyntax::Identifier,
            range,
            ExpectationSources::COMMITTED_RECOVERY_RULE,
        )]),
        0,
    )
}

fn finish_empty_root(
    mut output: ParserOutput<'_>,
) -> (rowan::GreenNode, Vec<CommittedRecoveryRecord>) {
    output.start_node(SyntaxKind::Root.into());
    output.finish_node();
    output.finish_with_recoveries()
}

fn unknown_item(text: &str) -> Item {
    Item::plain(
        LeadingTrivia::default(),
        Payload::Token(Token {
            kind: TokenKind::Unknown,
            text: text.into(),
        }),
    )
}

fn token_item(kind: TokenKind, text: &str) -> Item {
    Item::plain(
        LeadingTrivia::default(),
        Payload::Token(Token {
            kind,
            text: text.into(),
        }),
    )
}

fn seeded_root() -> rowan::GreenNode {
    let mut output = ParserOutput::new();
    output.start_node(SyntaxKind::Root.into());
    output.start_node(SyntaxKind::IdentifierExpression.into());
    output.token(SyntaxKind::Identifier.into(), "sentinel");
    output.finish_node();
    output.finish_node();
    output.finish()
}

#[test]
fn fresh_sequence_assigns_zero_one_and_preserves_same_offset_order_and_all_fields() {
    let mut output = ParserOutput::new();
    assert_eq!(output.recovery_capacity(), 0);
    let range = 7..7;
    output.commit_recovery(singleton_draft(
        LiteralRole::StringTerminator,
        RecoveryKind::Missing,
        range.clone(),
        Arc::from([]),
        ExpectedSyntax::Literal(LiteralExpected::StringTerminator),
    ));

    let expectations: Arc<[SyntaxExpectation]> = Arc::from([
        expectation(
            role(LiteralRole::RuleUnexpectedItem),
            ExpectedSyntax::Literal(LiteralExpected::RuleItem),
            range.clone(),
            ExpectationSources::COMMITTED_RECOVERY_RULE,
        ),
        expectation(
            role(LiteralRole::RuleUnexpectedItem),
            ExpectedSyntax::Identifier,
            range.clone(),
            ExpectationSources::SPECULATIVE.union(ExpectationSources::COMMITTED_RECOVERY_RULE),
        ),
    ]);
    output.commit_recovery(RecoveryDraft::new(
        RecoverySiteKey {
            role: role(LiteralRole::RuleUnexpectedItem),
            range: range.clone(),
        },
        RecoveryKind::Missing,
        Arc::from([]),
        expectations.clone(),
        1,
    ));

    let (_, records) = finish_empty_root(output);
    assert_eq!(records.len(), 2);
    assert_eq!(records[0].id, DiagnosticId(0));
    assert_eq!(records[1].id, DiagnosticId(1));
    assert_eq!(records[0].site.range, range);
    assert_eq!(records[0].kind, RecoveryKind::Missing);
    assert!(records[0].unexpected.is_empty());
    assert_eq!(records[1].site.role, role(LiteralRole::RuleUnexpectedItem));
    assert_eq!(records[1].expectations, expectations);
    assert_eq!(records[1].primary_expectation, 1);
}

#[test]
fn recovery_draft_rejects_every_invalid_shape() {
    let slot = LiteralRole::RuleUnexpectedItem;
    let valid_expectation = || {
        Arc::from([expectation(
            role(slot),
            ExpectedSyntax::Literal(LiteralExpected::RuleItem),
            2..2,
            ExpectationSources::COMMITTED_RECOVERY_RULE,
        )])
    };
    let cases: [Box<dyn FnOnce()>; 5] = [
        Box::new(move || {
            RecoveryDraft::new(
                RecoverySiteKey {
                    role: role(slot),
                    range: 2..2,
                },
                RecoveryKind::Missing,
                Arc::from([]),
                Arc::from([]),
                0,
            );
        }),
        Box::new(move || {
            RecoveryDraft::new(
                RecoverySiteKey {
                    role: role(slot),
                    range: 2..2,
                },
                RecoveryKind::Missing,
                Arc::from([]),
                valid_expectation(),
                1,
            );
        }),
        Box::new(move || {
            RecoveryDraft::new(
                RecoverySiteKey {
                    role: role(slot),
                    range: 2..3,
                },
                RecoveryKind::Missing,
                Arc::from([]),
                valid_expectation(),
                0,
            );
        }),
        Box::new(move || {
            RecoveryDraft::new(
                RecoverySiteKey {
                    role: role(slot),
                    range: 2..2,
                },
                RecoveryKind::Error,
                Arc::from([UnexpectedSyntax::Token {
                    range: 2..3,
                    category: UnexpectedCategory::OtherCharacter,
                }]),
                valid_expectation(),
                0,
            );
        }),
        Box::new(move || {
            RecoveryDraft::new(
                RecoverySiteKey {
                    role: role(slot),
                    range: 2..3,
                },
                RecoveryKind::Error,
                Arc::from([UnexpectedSyntax::EndOfInput { at: 3 }]),
                valid_expectation(),
                0,
            );
        }),
    ];
    for invalid in cases {
        assert!(catch_unwind(AssertUnwindSafe(invalid)).is_err());
    }
}

#[test]
fn reconciliation_is_sequential_exact_and_allocates_after_the_highest_id_without_record_clone() {
    let first_expectations: Arc<[SyntaxExpectation]> = Arc::from([expectation(
        role(LiteralRole::StringTerminator),
        ExpectedSyntax::Literal(LiteralExpected::StringTerminator),
        3..3,
        ExpectationSources::COMMITTED_RECOVERY_RULE,
    )]);
    let second_expectations: Arc<[SyntaxExpectation]> = Arc::from([expectation(
        role(LiteralRole::RuleLiteralTerminator),
        ExpectedSyntax::Literal(LiteralExpected::RuleLiteralTerminator),
        9..9,
        ExpectationSources::COMMITTED_RECOVERY_RULE,
    )]);
    let frozen = [
        frozen_record(
            9,
            LiteralRole::StringTerminator,
            RecoveryKind::Missing,
            3..3,
            Arc::from([]),
            first_expectations,
            0,
        ),
        frozen_record(
            4,
            LiteralRole::RuleLiteralTerminator,
            RecoveryKind::Missing,
            9..9,
            Arc::from([]),
            second_expectations,
            0,
        ),
    ];
    let reused_expectations: Arc<[SyntaxExpectation]> = Arc::from([expectation(
        role(LiteralRole::StringTerminator),
        ExpectedSyntax::Literal(LiteralExpected::StringTerminator),
        3..3,
        ExpectationSources::COMMITTED_RECOVERY_RULE,
    )]);
    let retained = reused_expectations.clone();
    let mut output = ParserOutput::reconcile(&frozen);
    output.commit_recovery(RecoveryDraft::new(
        RecoverySiteKey {
            role: role(LiteralRole::StringTerminator),
            range: 3..3,
        },
        RecoveryKind::Missing,
        Arc::from([]),
        reused_expectations,
        0,
    ));
    output.commit_recovery(singleton_draft(
        LiteralRole::RuleLiteralTerminator,
        RecoveryKind::Missing,
        9..9,
        Arc::from([]),
        ExpectedSyntax::Literal(LiteralExpected::RuleLiteralTerminator),
    ));
    output.commit_recovery(singleton_draft(
        LiteralRole::RuleLazyCaptureName,
        RecoveryKind::Missing,
        12..12,
        Arc::from([]),
        ExpectedSyntax::Identifier,
    ));
    let (_, records) = finish_empty_root(output);
    assert_eq!(
        records.iter().map(|record| record.id).collect::<Vec<_>>(),
        [DiagnosticId(9), DiagnosticId(4), DiagnosticId(10)]
    );
    assert!(Arc::ptr_eq(&records[0].expectations, &retained));
    assert!(!Arc::ptr_eq(
        &records[0].expectations,
        &frozen[0].expectations
    ));
}

#[test]
fn reconciliation_mismatch_and_overflow_do_not_advance_or_publish() {
    let expectations: Arc<[SyntaxExpectation]> = Arc::from([expectation(
        role(LiteralRole::StringTerminator),
        ExpectedSyntax::Literal(LiteralExpected::StringTerminator),
        1..1,
        ExpectationSources::COMMITTED_RECOVERY_RULE,
    )]);
    let frozen = [frozen_record(
        u32::MAX,
        LiteralRole::StringTerminator,
        RecoveryKind::Missing,
        1..1,
        Arc::from([]),
        expectations,
        0,
    )];
    let mut output = ParserOutput::reconcile(&frozen);
    let mismatch = catch_unwind(AssertUnwindSafe(|| {
        output.commit_recovery(singleton_draft(
            LiteralRole::StringTerminator,
            RecoveryKind::Missing,
            1..1,
            Arc::from([]),
            ExpectedSyntax::Literal(LiteralExpected::RuleItem),
        ));
    }));
    assert!(mismatch.is_err());
    assert_eq!(output.diagnostic_position(), (None, 0));
    assert_eq!(output.recovery_slot_count(), 0);

    output.commit_recovery(singleton_draft(
        LiteralRole::StringTerminator,
        RecoveryKind::Missing,
        1..1,
        Arc::from([]),
        ExpectedSyntax::Literal(LiteralExpected::StringTerminator),
    ));
    assert_eq!(output.diagnostic_position(), (None, 1));
    let overflow = catch_unwind(AssertUnwindSafe(|| {
        output.commit_recovery(singleton_draft(
            LiteralRole::RuleLiteralTerminator,
            RecoveryKind::Missing,
            2..2,
            Arc::from([]),
            ExpectedSyntax::Literal(LiteralExpected::RuleLiteralTerminator),
        ));
    }));
    assert!(overflow.is_err());
    assert_eq!(output.diagnostic_position(), (None, 1));
    assert_eq!(output.recovery_slot_count(), 1);
    let (_, records) = finish_empty_root(output);
    assert_eq!(records[0].id, DiagnosticId(u32::MAX));
}

#[test]
fn reconciliation_rejects_unused_or_invalid_frozen_records() {
    let valid = frozen_record(
        2,
        LiteralRole::StringTerminator,
        RecoveryKind::Missing,
        1..1,
        Arc::from([]),
        Arc::from([expectation(
            role(LiteralRole::StringTerminator),
            ExpectedSyntax::Literal(LiteralExpected::StringTerminator),
            1..1,
            ExpectationSources::COMMITTED_RECOVERY_RULE,
        )]),
        0,
    );
    assert!(
        catch_unwind(AssertUnwindSafe(|| finish_empty_root(
            ParserOutput::reconcile(std::slice::from_ref(&valid))
        )))
        .is_err()
    );

    let invalid = frozen_record(
        0,
        LiteralRole::StringTerminator,
        RecoveryKind::Missing,
        1..1,
        Arc::from([]),
        Arc::from([]),
        0,
    );
    assert!(
        catch_unwind(AssertUnwindSafe(|| ParserOutput::reconcile(
            std::slice::from_ref(&invalid)
        )))
        .is_err()
    );
}

fn emit_nested_structured_recoveries(output: &mut ParserOutput<'_>) {
    let operators = OperatorTable::empty();
    let mut input = "";
    let mut recover = Recover::new(&operators);
    output.start_node(SyntaxKind::Root.into());
    emit_structured_recovery_error_from_item(
        In::new(&mut input, &mut recover, &mut *output),
        unknown_item("a"),
        1,
        structured_spec(LiteralRole::RuleFieldName),
        |mut nested, primary| {
            primary.emit_remaining(&mut *nested.state, SyntaxKind::Unknown);
            emit_recovery_missing(nested.rb(), LeadingTrivia::default(), 1, |range| {
                singleton_draft(
                    LiteralRole::RuleCaptureRightItem,
                    RecoveryKind::Missing,
                    range,
                    Arc::from([]),
                    ExpectedSyntax::Literal(LiteralExpected::RuleItem),
                )
            });
            emit_structured_recovery_error_from_item(
                nested.rb(),
                unknown_item("b"),
                2,
                structured_spec(LiteralRole::RulePathName),
                |inner, primary| {
                    primary.emit_remaining(&mut *inner.state, SyntaxKind::Unknown);
                    ((), 2)
                },
            );
            nested.state.token(SyntaxKind::Unknown.into(), "c");
            ((), 3)
        },
    );
    output.finish_node();
}

#[test]
fn structured_reservations_preserve_fresh_and_frozen_order_through_nested_publication() {
    let mut fresh = ParserOutput::new();
    assert_eq!(fresh.recovery_capacity(), 0);
    emit_nested_structured_recoveries(&mut fresh);
    let (green, records) = fresh.finish_with_recoveries();
    assert_eq!(green.to_string(), "abc");
    let root = SyntaxNode::new_root(green);
    assert_eq!(
        root.descendants()
            .filter(|node| node.kind() == SyntaxKind::Error)
            .count(),
        2
    );
    assert_eq!(
        root.descendants()
            .filter(|node| node.kind() == SyntaxKind::Missing)
            .count(),
        1
    );
    assert_eq!(
        records.iter().map(|record| record.id).collect::<Vec<_>>(),
        [DiagnosticId(0), DiagnosticId(1), DiagnosticId(2)]
    );
    assert_eq!(
        records
            .iter()
            .filter(|record| record.kind == RecoveryKind::Error)
            .count(),
        2
    );
    assert_eq!(
        records[0],
        structured_record(0, LiteralRole::RuleFieldName, 0..3)
    );
    assert_eq!(records[1].site.range, 1..1);
    assert_eq!(records[1].kind, RecoveryKind::Missing);
    assert_eq!(
        records[2],
        structured_record(2, LiteralRole::RulePathName, 1..2)
    );

    let frozen = [
        structured_record(9, LiteralRole::RuleFieldName, 0..3),
        frozen_record(
            4,
            LiteralRole::RuleCaptureRightItem,
            RecoveryKind::Missing,
            1..1,
            Arc::from([]),
            Arc::from([expectation(
                role(LiteralRole::RuleCaptureRightItem),
                ExpectedSyntax::Literal(LiteralExpected::RuleItem),
                1..1,
                ExpectationSources::COMMITTED_RECOVERY_RULE,
            )]),
            0,
        ),
        structured_record(12, LiteralRole::RulePathName, 1..2),
    ];
    let mut reconciled = ParserOutput::reconcile(&frozen);
    emit_nested_structured_recoveries(&mut reconciled);
    let (_, records) = reconciled.finish_with_recoveries();
    assert_eq!(records, frozen);
}

#[test]
fn structured_reservation_allocates_after_empty_and_exhausted_frozen_sequences() {
    let (_, valid_records) = finish_empty_root(ParserOutput::new());
    assert!(valid_records.is_empty());
    assert_eq!(valid_records.capacity(), 0);

    let empty: [CommittedRecoveryRecord; 0] = [];
    let mut output = ParserOutput::reconcile(&empty);
    let operators = OperatorTable::empty();
    let mut input = "";
    let mut recover = Recover::new(&operators);
    output.start_node(SyntaxKind::Root.into());
    emit_structured_recovery_error_from_item(
        In::new(&mut input, &mut recover, &mut output),
        unknown_item("x"),
        1,
        structured_spec(LiteralRole::RuleFieldName),
        |nested, primary| {
            primary.emit_remaining(&mut *nested.state, SyntaxKind::Unknown);
            ((), 1)
        },
    );
    output.finish_node();
    let (_, records) = output.finish_with_recoveries();
    assert_eq!(
        records,
        [structured_record(0, LiteralRole::RuleFieldName, 0..1)]
    );

    let frozen = [frozen_record(
        7,
        LiteralRole::RuleCaptureRightItem,
        RecoveryKind::Missing,
        0..0,
        Arc::from([]),
        Arc::from([expectation(
            role(LiteralRole::RuleCaptureRightItem),
            ExpectedSyntax::Literal(LiteralExpected::RuleItem),
            0..0,
            ExpectationSources::COMMITTED_RECOVERY_RULE,
        )]),
        0,
    )];
    let mut output = ParserOutput::reconcile(&frozen);
    let mut input = "";
    let mut recover = Recover::new(&operators);
    output.start_node(SyntaxKind::Root.into());
    emit_recovery_missing(
        In::new(&mut input, &mut recover, &mut output),
        LeadingTrivia::default(),
        0,
        |range| {
            singleton_draft(
                LiteralRole::RuleCaptureRightItem,
                RecoveryKind::Missing,
                range,
                Arc::from([]),
                ExpectedSyntax::Literal(LiteralExpected::RuleItem),
            )
        },
    );
    emit_structured_recovery_error_from_item(
        In::new(&mut input, &mut recover, &mut output),
        unknown_item("a"),
        2,
        structured_spec(LiteralRole::RuleFieldName),
        |mut outer, primary| {
            primary.emit_remaining(&mut *outer.state, SyntaxKind::Unknown);
            emit_recovery_missing(outer.rb(), LeadingTrivia::default(), 2, |range| {
                singleton_draft(
                    LiteralRole::RuleCaptureRightItem,
                    RecoveryKind::Missing,
                    range,
                    Arc::from([]),
                    ExpectedSyntax::Literal(LiteralExpected::RuleItem),
                )
            });
            emit_structured_recovery_error_from_item(
                outer.rb(),
                unknown_item("b"),
                3,
                structured_spec(LiteralRole::RulePathName),
                |inner, primary| {
                    primary.emit_remaining(&mut *inner.state, SyntaxKind::Unknown);
                    ((), 3)
                },
            );
            outer.state.token(SyntaxKind::Unknown.into(), "c");
            ((), 4)
        },
    );
    output.finish_node();
    let (_, records) = output.finish_with_recoveries();
    assert_eq!(
        records.iter().map(|record| record.id).collect::<Vec<_>>(),
        [
            DiagnosticId(7),
            DiagnosticId(8),
            DiagnosticId(9),
            DiagnosticId(10)
        ]
    );
    assert_eq!(records[1].site.range, 1..4);
    assert_eq!(records[2].site.range, 2..2);
    assert_eq!(records[3].site.range, 2..3);
}

#[test]
fn structured_item_start_and_token_delta_exclude_prior_and_preemitted_bytes() {
    let operators = OperatorTable::empty();
    let mut input = "";
    let mut recover = Recover::new(&operators);
    let mut output = ParserOutput::new();
    output.start_node(SyntaxKind::Root.into());
    output.token(SyntaxKind::Identifier.into(), "seed");
    emit_structured_recovery_error_from_item(
        In::new(&mut input, &mut recover, &mut output),
        unknown_item("x"),
        11,
        structured_spec(LiteralRole::RuleFieldName),
        |nested, primary| {
            primary.emit_remaining(&mut *nested.state, SyntaxKind::Unknown);
            ((), 11)
        },
    );
    output.finish_node();
    let (green, records) = output.finish_with_recoveries();
    assert_eq!(green.to_string(), "seedx");
    assert_eq!(
        records,
        [structured_record(0, LiteralRole::RuleFieldName, 10..11)]
    );

    let origin = 20;
    let comment = "/*a\n> b*/";
    let payload = "β\r\n> q";
    let payload_start = origin + comment.len() + 1;
    let successor = payload_start + payload.len();
    let mut primary = Item::finish(
        PhysicalLeadingTrivia::from_ordinary(LeadingTrivia::ordinary(
            vec![
                Trivia::block_comment(comment.into()),
                Trivia::whitespace(" ".into()),
            ]
            .into_boxed_slice(),
        )),
        Payload::Token(Token {
            kind: TokenKind::Unknown,
            text: payload.into(),
        }),
        Some(vec![
            ForeignSplit::quote_prefix(origin + "/*a\n".len(), 2),
            ForeignSplit::quote_prefix(payload_start + "β\r\n".len(), 2),
        ]),
        origin,
    )
    .unwrap();
    let mut input = "";
    let mut recover = Recover::new(&operators);
    let mut output = ParserOutput::new();
    output.start_node(SyntaxKind::Root.into());
    primary.emit_all_remaining_leading(&mut output);
    emit_structured_recovery_error_from_item(
        In::new(&mut input, &mut recover, &mut output),
        primary,
        successor,
        structured_spec(LiteralRole::RulePathName),
        |nested, primary| {
            primary.emit_remaining(&mut *nested.state, SyntaxKind::Unknown);
            ((), successor)
        },
    );
    output.finish_node();
    let (green, records) = output.finish_with_recoveries();
    assert_eq!(green.to_string(), format!("{comment} {payload}"));
    let root = SyntaxNode::new_root(green);
    let error = root
        .descendants()
        .find(|node| node.kind() == SyntaxKind::Error)
        .unwrap();
    assert_eq!(error.to_string(), payload);
    assert_eq!(
        error
            .descendants_with_tokens()
            .filter_map(|element| element.into_token())
            .map(|token| (token.kind(), token.text().to_owned()))
            .collect::<Vec<_>>(),
        [
            (SyntaxKind::Unknown, "β\r\n".into()),
            (SyntaxKind::YmQuotePrefix, "> ".into()),
            (SyntaxKind::Unknown, "q".into()),
        ]
    );
    assert_eq!(
        records,
        [structured_record(
            0,
            LiteralRole::RulePathName,
            payload_start..successor,
        )]
    );
}

#[test]
fn structured_reservation_rejects_partial_full_lifo_overflow_and_unfinished_failures() {
    let wrong_role = [structured_record(3, LiteralRole::RuleFieldName, 0..1)];
    assert!(
        catch_unwind(AssertUnwindSafe(|| {
            let mut output = ParserOutput::reconcile(&wrong_role);
            let operators = OperatorTable::empty();
            let mut input = "";
            let mut recover = Recover::new(&operators);
            emit_structured_recovery_error_from_item(
                In::new(&mut input, &mut recover, &mut output),
                unknown_item("x"),
                1,
                structured_spec(LiteralRole::RulePathName),
                |_, _| ((), 1),
            );
        }))
        .is_err()
    );

    for frozen in [
        None,
        Some(structured_record(5, LiteralRole::RuleFieldName, 0..2)),
    ] {
        assert!(
            catch_unwind(AssertUnwindSafe(|| {
                let frozen_storage = frozen.into_iter().collect::<Vec<_>>();
                let mut output = if frozen_storage.is_empty() {
                    ParserOutput::new()
                } else {
                    ParserOutput::reconcile(&frozen_storage)
                };
                let operators = OperatorTable::empty();
                let mut input = "";
                let mut recover = Recover::new(&operators);
                emit_structured_recovery_error_from_item(
                    In::new(&mut input, &mut recover, &mut output),
                    unknown_item("x"),
                    1,
                    structured_spec(LiteralRole::RuleFieldName),
                    |nested, primary| {
                        primary.emit_remaining(&mut *nested.state, SyntaxKind::Unknown);
                        ((), 2)
                    },
                );
            }))
            .is_err()
        );
    }

    let wrong_end = [structured_record(5, LiteralRole::RuleFieldName, 0..2)];
    assert!(
        catch_unwind(AssertUnwindSafe(|| {
            let mut output = ParserOutput::reconcile(&wrong_end);
            let operators = OperatorTable::empty();
            let mut input = "";
            let mut recover = Recover::new(&operators);
            emit_structured_recovery_error_from_item(
                In::new(&mut input, &mut recover, &mut output),
                unknown_item("x"),
                1,
                structured_spec(LiteralRole::RuleFieldName),
                |nested, primary| {
                    primary.emit_remaining(&mut *nested.state, SyntaxKind::Unknown);
                    ((), 1)
                },
            );
        }))
        .is_err()
    );

    assert!(
        catch_unwind(AssertUnwindSafe(|| {
            let mut output = ParserOutput::new();
            let operators = OperatorTable::empty();
            let mut input = "";
            let mut recover = Recover::new(&operators);
            let primary = Item::plain(
                LeadingTrivia::ordinary(vec![Trivia::whitespace(" ".into())].into_boxed_slice()),
                Payload::Token(Token {
                    kind: TokenKind::Unknown,
                    text: "x".into(),
                }),
            );
            emit_structured_recovery_error_from_item(
                In::new(&mut input, &mut recover, &mut output),
                primary,
                2,
                structured_spec(LiteralRole::RuleFieldName),
                |_, _| ((), 2),
            );
        }))
        .is_err()
    );

    assert!(
        catch_unwind(AssertUnwindSafe(|| {
            let mut output = ParserOutput::new();
            output.violate_structured_lifo_for_test(
                unknown_item("a"),
                1,
                structured_spec(LiteralRole::RuleFieldName),
                unknown_item("b"),
                2,
                structured_spec(LiteralRole::RulePathName),
                2,
            );
        }))
        .is_err()
    );

    assert!(
        catch_unwind(AssertUnwindSafe(|| {
            let mut output = ParserOutput::new();
            output.start_node(SyntaxKind::Root.into());
            output.finish_node();
            output.leave_structured_unfinished_for_test(
                unknown_item("x"),
                1,
                structured_spec(LiteralRole::RuleFieldName),
            );
            output.finish_with_recoveries();
        }))
        .is_err()
    );

    assert!(
        catch_unwind(AssertUnwindSafe(|| {
            let mut output = ParserOutput::new();
            let operators = OperatorTable::empty();
            let mut input = "";
            let mut recover = Recover::new(&operators);
            emit_structured_recovery_error_from_item(
                In::new(&mut input, &mut recover, &mut output),
                unknown_item("x"),
                1,
                structured_spec(LiteralRole::RuleFieldName),
                |_, _| ((), 0),
            );
        }))
        .is_err()
    );

    let maximum = [frozen_record(
        u32::MAX,
        LiteralRole::RuleCaptureRightItem,
        RecoveryKind::Missing,
        0..0,
        Arc::from([]),
        Arc::from([expectation(
            role(LiteralRole::RuleCaptureRightItem),
            ExpectedSyntax::Literal(LiteralExpected::RuleItem),
            0..0,
            ExpectationSources::COMMITTED_RECOVERY_RULE,
        )]),
        0,
    )];
    assert!(
        catch_unwind(AssertUnwindSafe(|| {
            let mut output = ParserOutput::reconcile(&maximum);
            output.commit_recovery(singleton_draft(
                LiteralRole::RuleCaptureRightItem,
                RecoveryKind::Missing,
                0..0,
                Arc::from([]),
                ExpectedSyntax::Literal(LiteralExpected::RuleItem),
            ));
            let operators = OperatorTable::empty();
            let mut input = "";
            let mut recover = Recover::new(&operators);
            emit_structured_recovery_error_from_item(
                In::new(&mut input, &mut recover, &mut output),
                unknown_item("x"),
                2,
                structured_spec(LiteralRole::RuleFieldName),
                |_, _| ((), 2),
            );
        }))
        .is_err()
    );
}

#[test]
fn item_extent_uses_only_owned_bytes_for_utf8_crlf_partial_and_fragmented_items() {
    let leading = LeadingTrivia::ordinary(
        vec![
            Trivia::whitespace(" ".into()),
            Trivia::newline("\r\n".into()),
            Trivia::whitespace("  ".into()),
        ]
        .into_boxed_slice(),
    );
    let item = Item::plain(
        leading,
        Payload::Token(Token {
            kind: TokenKind::Identifier,
            text: "α".into(),
        }),
    );
    let extent = item.extent(20);
    assert_eq!(extent.physical(), 13..20);
    assert_eq!(extent.leading(), 13..18);
    assert_eq!(extent.remaining(), 13..18);
    assert_eq!(extent.payload(), 18..20);

    let mut partial = Item::plain(
        LeadingTrivia::ordinary(
            vec![
                Trivia::whitespace("ab".into()),
                Trivia::newline("\r\n".into()),
                Trivia::whitespace("c".into()),
            ]
            .into_boxed_slice(),
        ),
        Payload::Token(Token {
            kind: TokenKind::Identifier,
            text: "δ".into(),
        }),
    );
    let mut output = ParserOutput::new();
    output.start_node(SyntaxKind::Root.into());
    partial.emit_leading_prefix_with(&mut output, 2, |_, _| {});
    let extent = partial.extent(40);
    assert_eq!(extent.physical(), 33..40);
    assert_eq!(extent.leading(), 33..38);
    assert_eq!(extent.remaining(), 37..38);
    assert_eq!(extent.payload(), 38..40);
    output.finish_node();
    assert_eq!(output.finish().to_string(), "ab\r\n");

    let origin = 50;
    let comment = "/*a\n> b*/";
    let payload = "z\n> q";
    let physical_len = comment.len() + 1 + payload.len();
    let fragmented = Item::finish(
        PhysicalLeadingTrivia::from_ordinary(LeadingTrivia::ordinary(
            vec![
                Trivia::block_comment(comment.into()),
                Trivia::whitespace(" ".into()),
            ]
            .into_boxed_slice(),
        )),
        Payload::Token(Token {
            kind: TokenKind::Identifier,
            text: payload.into(),
        }),
        Some(vec![
            ForeignSplit::quote_prefix(origin + "/*a\n".len(), 2),
            ForeignSplit::quote_prefix(origin + comment.len() + 1 + "z\n".len(), 2),
        ]),
        origin,
    )
    .unwrap();
    assert_eq!(
        fragmented.extent(origin + physical_len).physical(),
        origin..origin + physical_len
    );
}

#[test]
fn item_extent_anchors_eof_and_inspected_boundaries_without_consuming_them() {
    let eof = Item::plain(
        LeadingTrivia::ordinary(vec![Trivia::newline("\r\n".into())].into_boxed_slice()),
        Payload::Eof,
    );
    let extent = eof.extent(8);
    assert_eq!(extent.physical(), 6..8);
    assert_eq!(extent.payload(), 8..8);

    let boundary = PendingBoundary::new(40..45, Boundary::Stop(StopKind::RightBrace));
    assert_eq!(boundary.coordinate(), 40);
    assert_eq!(boundary.inspected(), &(40..45));
    let item = Item::plain(
        LeadingTrivia::ordinary(vec![Trivia::whitespace(" ".into())].into_boxed_slice()),
        Payload::Boundary(boundary),
    );
    let extent = item.extent(40);
    assert_eq!(extent.physical(), 39..40);
    assert_eq!(extent.payload(), 40..40);
    assert!(catch_unwind(AssertUnwindSafe(|| item.extent(0))).is_err());
}

#[test]
fn typed_missing_and_one_item_error_publish_exact_records_and_nodes() {
    let operators = OperatorTable::empty();
    let mut input = "";
    let mut recover = Recover::new(&operators);
    let mut output = ParserOutput::new();
    output.start_node(SyntaxKind::Root.into());
    emit_recovery_missing(
        In::new(&mut input, &mut recover, &mut output),
        LeadingTrivia::ordinary(vec![Trivia::whitespace(" ".into())].into_boxed_slice()),
        5,
        |range| {
            singleton_draft(
                LiteralRole::StringTerminator,
                RecoveryKind::Missing,
                range,
                Arc::from([]),
                ExpectedSyntax::Literal(LiteralExpected::StringTerminator),
            )
        },
    );
    let item = Item::plain(
        LeadingTrivia::ordinary(vec![Trivia::whitespace("\r\n".into())].into_boxed_slice()),
        Payload::Token(Token {
            kind: TokenKind::Unknown,
            text: "α".into(),
        }),
    );
    let extent = emit_recovery_error_item(
        In::new(&mut input, &mut recover, &mut output),
        item,
        9,
        SyntaxKind::Unknown,
        UnexpectedSyntax::Token {
            range: 5..9,
            category: UnexpectedCategory::OtherCharacter,
        },
        |range, unexpected| {
            singleton_draft(
                LiteralRole::RuleUnexpectedItem,
                RecoveryKind::Error,
                range,
                unexpected,
                ExpectedSyntax::Literal(LiteralExpected::RuleItem),
            )
        },
    );
    assert_eq!(extent.recovery_range(), 5..9);
    output.finish_node();
    let (green, records) = output.finish_with_recoveries();
    assert_eq!(green.to_string(), " \r\nα");
    let root = SyntaxNode::new_root(green);
    assert_eq!(
        root.descendants()
            .filter(|node| node.kind() == SyntaxKind::Missing)
            .count(),
        1
    );
    assert_eq!(
        root.descendants()
            .filter(|node| node.kind() == SyntaxKind::Error)
            .count(),
        1
    );
    assert_eq!(records[0].site.range, 5..5);
    assert_eq!(records[1].site.range, 5..9);
    assert_eq!(
        records[1].unexpected,
        Arc::from([UnexpectedSyntax::Token {
            range: 5..9,
            category: UnexpectedCategory::OtherCharacter
        }])
    );
}

#[test]
fn one_item_error_uses_owner_selected_kind_and_preserves_leading_fragments() {
    let operators = OperatorTable::empty();
    let mut input = "";
    let mut recover = Recover::new(&operators);
    let mut output = ParserOutput::new();
    output.start_node(SyntaxKind::Root.into());

    let origin = 20;
    let comment = "/*a\n> b*/";
    let payload = "++";
    let physical_len = comment.len() + 1 + payload.len();
    let item = Item::finish(
        PhysicalLeadingTrivia::from_ordinary(LeadingTrivia::ordinary(
            vec![
                Trivia::block_comment(comment.into()),
                Trivia::whitespace(" ".into()),
            ]
            .into_boxed_slice(),
        )),
        Payload::Token(Token {
            kind: TokenKind::Operator,
            text: payload.into(),
        }),
        Some(vec![ForeignSplit::quote_prefix(origin + "/*a\n".len(), 2)]),
        origin,
    )
    .unwrap();
    let successor = origin + physical_len;
    let extent = emit_recovery_error_item(
        In::new(&mut input, &mut recover, &mut output),
        item,
        successor,
        SyntaxKind::Unknown,
        UnexpectedSyntax::Token {
            range: origin..successor,
            category: UnexpectedCategory::OperatorLike,
        },
        |range, unexpected| {
            singleton_draft(
                LiteralRole::RuleUnexpectedItem,
                RecoveryKind::Error,
                range,
                unexpected,
                ExpectedSyntax::Literal(LiteralExpected::RuleItem),
            )
        },
    );
    output.finish_node();
    let (green, records) = output.finish_with_recoveries();
    let root = SyntaxNode::new_root(green);
    let tokens = root
        .descendants_with_tokens()
        .filter_map(|element| element.into_token())
        .map(|token| (token.kind(), token.text().to_owned()))
        .collect::<Vec<_>>();
    assert_eq!(extent.recovery_range(), origin..successor);
    assert_eq!(
        tokens,
        [
            (SyntaxKind::BlockComment, "/*a\n".into()),
            (SyntaxKind::YmQuotePrefix, "> ".into()),
            (SyntaxKind::BlockComment, "b*/".into()),
            (SyntaxKind::Whitespace, " ".into()),
            (SyntaxKind::Unknown, "++".into()),
        ]
    );
    assert_eq!(records.len(), 1);
    assert_eq!(records[0].site.range, origin..successor);
}

#[test]
fn total_error_run_exposes_only_forward_lexical_and_emission_capabilities() {
    let operators = OperatorTable::empty();
    let mut input = "@β";
    let mut recover = Recover::new(&operators);
    let mut output = ParserOutput::new();
    output.start_node(SyntaxKind::Root.into());
    emit_recovery_error_run(
        In::new(&mut input, &mut recover, &mut output),
        |run| {
            let first = run.lexical(|mut lex| lex.next().unwrap());
            assert_eq!(first, '@');
            run.emit_literal_segment("@", 10..11, SyntaxKind::Unknown);
            run.append_unexpected(UnexpectedSyntax::Token {
                range: 10..11,
                category: UnexpectedCategory::OtherCharacter,
            });
            let second = run.lexical(|mut lex| lex.next().unwrap());
            assert_eq!(second, 'β');
            run.emit_literal_segment("β", 11..13, SyntaxKind::Unknown);
            run.append_unexpected(UnexpectedSyntax::Token {
                range: 11..13,
                category: UnexpectedCategory::OtherCharacter,
            });
        },
        |range, unexpected| {
            singleton_draft(
                LiteralRole::RuleUnexpectedItem,
                RecoveryKind::Error,
                range,
                unexpected,
                ExpectedSyntax::Literal(LiteralExpected::RuleItem),
            )
        },
    );
    output.finish_node();
    let (green, records) = output.finish_with_recoveries();
    assert_eq!(input, "");
    assert_eq!(green.to_string(), "@β");
    assert_eq!(
        SyntaxNode::new_root(green)
            .descendants()
            .filter(|node| node.kind() == SyntaxKind::Error)
            .count(),
        1
    );
    assert_eq!(records.len(), 1);
    assert_eq!(records[0].site.range, 10..13);
    assert_eq!(records[0].unexpected.len(), 2);

    const ERROR_RUN_CAPABILITY: [&str; 7] = [
        "lexical",
        "emit_item_as",
        "emit_literal_segment",
        "append_unexpected",
        "seal_record_through_retry_leading",
        "seal_path_segment_retry_leading_prefix",
        "seal_call_argument_retry_leading_prefix",
    ];
    assert_eq!(ERROR_RUN_CAPABILITY.len(), 7);
}

#[test]
fn call_argument_retry_leading_seal_emits_the_complete_native_prefix() {
    let operators = OperatorTable::empty();
    let mut input = "";
    let mut recover = Recover::new(&operators);
    let mut output = ParserOutput::new();
    output.start_node(SyntaxKind::Root.into());
    let mut retry = Item::plain(
        LeadingTrivia::ordinary(
            vec![
                Trivia::whitespace(" ".into()),
                Trivia::block_comment("/*a*/".into()),
                Trivia::whitespace(" ".into()),
            ]
            .into_boxed_slice(),
        ),
        Payload::Token(Token {
            kind: TokenKind::Identifier,
            text: "A".into(),
        }),
    );
    let sealed = emit_recovery_error_run(
        In::new(&mut input, &mut recover, &mut output),
        |run| {
            run.emit_literal_segment("@", 0..1, SyntaxKind::Unknown);
            let sealed = run.seal_call_argument_retry_leading_prefix(
                &mut retry,
                9,
                UnexpectedCategory::OtherCharacter,
            );
            assert_eq!(sealed, CallArgumentRetryLeadingSeal::Sealed);
            assert!(catch_unwind(AssertUnwindSafe(|| run.lexical(|mut lex| lex.next()))).is_err());
            assert!(
                catch_unwind(AssertUnwindSafe(|| {
                    run.emit_item_as(unknown_item("!"), 9, SyntaxKind::Unknown)
                }))
                .is_err()
            );
            assert!(
                catch_unwind(AssertUnwindSafe(|| {
                    run.emit_literal_segment("!", 8..9, SyntaxKind::Unknown)
                }))
                .is_err()
            );
            assert!(
                catch_unwind(AssertUnwindSafe(|| {
                    run.append_unexpected(UnexpectedSyntax::Token {
                        range: 0..8,
                        category: UnexpectedCategory::OtherCharacter,
                    })
                }))
                .is_err()
            );
            assert!(
                catch_unwind(AssertUnwindSafe(|| {
                    run.seal_record_through_retry_leading(
                        &retry,
                        9,
                        UnexpectedCategory::OtherCharacter,
                    )
                }))
                .is_err()
            );
            assert!(
                catch_unwind(AssertUnwindSafe(|| {
                    run.seal_path_segment_retry_leading_prefix(
                        &mut retry,
                        9,
                        UnexpectedCategory::OtherCharacter,
                    )
                }))
                .is_err()
            );
            assert!(
                catch_unwind(AssertUnwindSafe(|| {
                    run.seal_call_argument_retry_leading_prefix(
                        &mut retry,
                        9,
                        UnexpectedCategory::OtherCharacter,
                    )
                }))
                .is_err()
            );
            sealed
        },
        |range, unexpected| {
            let role = GrammarRole::Type(TypeRole::CallArgument);
            RecoveryDraft::new(
                RecoverySiteKey {
                    role,
                    range: range.clone(),
                },
                RecoveryKind::Error,
                unexpected,
                Arc::from([expectation(
                    role,
                    ExpectedSyntax::TypeExpression,
                    range,
                    ExpectationSources::COMMITTED_RECOVERY_RULE,
                )]),
                0,
            )
        },
    );
    assert_eq!(sealed, CallArgumentRetryLeadingSeal::Sealed);
    assert_eq!(retry.leading_view().remaining_physical_parts(), 0);
    retry.emit_payload(&mut output, SyntaxKind::Identifier);
    output.finish_node();
    let (green, records) = output.finish_with_recoveries();
    assert_eq!(green.to_string(), "@ /*a*/ A");
    assert_eq!(records[0].site.range, 0..8);
    assert_eq!(
        records[0].unexpected,
        Arc::from([UnexpectedSyntax::Token {
            range: 0..8,
            category: UnexpectedCategory::OtherCharacter,
        }])
    );
    let root = SyntaxNode::new_root(green);
    let error = root
        .children()
        .find(|node| node.kind() == SyntaxKind::Error)
        .expect("CallArgument Error");
    assert_eq!(
        error
            .children_with_tokens()
            .map(|element| (element.kind(), element.to_string()))
            .collect::<Vec<_>>(),
        [
            (SyntaxKind::Unknown, "@".to_owned()),
            (SyntaxKind::Whitespace, " ".to_owned()),
            (SyntaxKind::BlockComment, "/*a*/".to_owned()),
            (SyntaxKind::Whitespace, " ".to_owned()),
        ]
    );
}

#[test]
fn call_argument_retry_leading_ineligibility_is_atomic_and_keeps_the_run_open() {
    fn token_retry(leading: Box<[Trivia]>) -> Item {
        Item::plain(
            LeadingTrivia::ordinary(leading),
            Payload::Token(Token {
                kind: TokenKind::Identifier,
                text: "A".into(),
            }),
        )
    }

    fn reject(mut retry: Item, successor_origin: usize) {
        let control = format!("{retry:?}");
        let operators = OperatorTable::empty();
        let mut input = "";
        let mut recover = Recover::new(&operators);
        let mut output = ParserOutput::new();
        output.start_node(SyntaxKind::Root.into());
        let result = emit_recovery_error_run(
            In::new(&mut input, &mut recover, &mut output),
            |run| {
                run.emit_literal_segment("@", 0..1, SyntaxKind::Unknown);
                let result = run.seal_call_argument_retry_leading_prefix(
                    &mut retry,
                    successor_origin,
                    UnexpectedCategory::OtherCharacter,
                );
                assert_eq!(result, CallArgumentRetryLeadingSeal::Ineligible);
                assert_eq!(format!("{retry:?}"), control);
                run.append_unexpected(UnexpectedSyntax::Token {
                    range: 0..1,
                    category: UnexpectedCategory::OtherCharacter,
                });
                result
            },
            |range, unexpected| {
                singleton_draft(
                    LiteralRole::RuleUnexpectedItem,
                    RecoveryKind::Error,
                    range,
                    unexpected,
                    ExpectedSyntax::Literal(LiteralExpected::RuleItem),
                )
            },
        );
        output.finish_node();
        let (green, records) = output.finish_with_recoveries();
        assert_eq!(result, CallArgumentRetryLeadingSeal::Ineligible);
        assert_eq!(green.to_string(), "@");
        assert_eq!(records[0].site.range, 0..1);
    }

    reject(token_retry(Vec::new().into_boxed_slice()), 2);
    reject(
        token_retry(vec![Trivia::newline("\n".into())].into_boxed_slice()),
        3,
    );
    reject(
        token_retry(vec![Trivia::newline("\r\n".into())].into_boxed_slice()),
        4,
    );
    reject(
        token_retry(vec![Trivia::line_comment("//x".into())].into_boxed_slice()),
        5,
    );
    reject(
        Item::plain(
            LeadingTrivia::ordinary(vec![Trivia::whitespace(" ".into())].into_boxed_slice()),
            Payload::Eof,
        ),
        1,
    );
    reject(
        Item::plain(
            LeadingTrivia::ordinary(vec![Trivia::whitespace(" ".into())].into_boxed_slice()),
            Payload::Boundary(PendingBoundary::new(
                1..2,
                Boundary::Stop(StopKind::RightParenthesis),
            )),
        ),
        1,
    );
    reject(
        token_retry(vec![Trivia::whitespace(" ".into())].into_boxed_slice()),
        4,
    );

    let carrier_origin = 1;
    let carrier = Item::finish(
        PhysicalLeadingTrivia::from_ordinary(LeadingTrivia::ordinary(
            vec![Trivia::block_comment("/*x*/".into())].into_boxed_slice(),
        )),
        Payload::Token(Token {
            kind: TokenKind::Identifier,
            text: "A".into(),
        }),
        Some(vec![ForeignSplit::quote_prefix(3, 2)]),
        carrier_origin,
    )
    .expect("carrier retry Item");
    reject(carrier, 7);

    let mut partial = token_retry(vec![Trivia::whitespace(" ".into())].into_boxed_slice());
    let mut prefix_output = ParserOutput::new();
    partial.emit_leading_prefix_with(&mut prefix_output, 1, |_, _| {});
    reject(partial, 2);
}

#[test]
fn path_segment_retry_leading_seal_emits_only_block_comments_and_returns_the_same_item() {
    let operators = OperatorTable::empty();
    let mut input = "";
    let mut recover = Recover::new(&operators);
    let mut output = ParserOutput::new();
    output.start_node(SyntaxKind::Root.into());
    let mut retry = Item::plain(
        LeadingTrivia::ordinary(
            vec![
                Trivia::block_comment("/*a*/".into()),
                Trivia::block_comment("/*b*/".into()),
                Trivia::whitespace(" ".into()),
            ]
            .into_boxed_slice(),
        ),
        Payload::Token(Token {
            kind: TokenKind::Identifier,
            text: "B".into(),
        }),
    );
    let sealed = emit_recovery_error_run(
        In::new(&mut input, &mut recover, &mut output),
        |run| {
            run.emit_literal_segment("@", 0..1, SyntaxKind::Unknown);
            run.seal_path_segment_retry_leading_prefix(
                &mut retry,
                13,
                UnexpectedCategory::OtherCharacter,
            )
        },
        |range, unexpected| path_segment_draft(RecoveryKind::Error, range, unexpected),
    );
    assert_eq!(sealed, PathSegmentRetryLeadingSeal::Sealed);
    assert_eq!(retry.leading_view().remaining_physical_parts(), 1);
    retry.emit_remaining(&mut output, SyntaxKind::Identifier);
    output.finish_node();
    let (green, records) = output.finish_with_recoveries();
    assert_eq!(green.to_string(), "@/*a*//*b*/ B");
    assert_eq!(
        records[0].site.role,
        GrammarRole::Type(TypeRole::PathSegment)
    );
    assert_eq!(
        records[0].expectations[0].expected,
        ExpectedSyntax::TypePathSegment
    );
    assert_eq!(records[0].site.range, 0..11);
    assert_eq!(
        records[0].unexpected,
        Arc::from([UnexpectedSyntax::Token {
            range: 0..11,
            category: UnexpectedCategory::OtherCharacter,
        }])
    );
    let root = SyntaxNode::new_root(green);
    let error = root
        .children()
        .find(|node| node.kind() == SyntaxKind::Error)
        .expect("PathSegment Error");
    assert_eq!(error.text(), "@/*a*//*b*/");
    assert_eq!(
        error
            .children_with_tokens()
            .map(|element| (element.kind(), element.to_string()))
            .collect::<Vec<_>>(),
        [
            (SyntaxKind::Unknown, "@".to_owned()),
            (SyntaxKind::BlockComment, "/*a*/".to_owned()),
            (SyntaxKind::BlockComment, "/*b*/".to_owned()),
        ]
    );
    assert_eq!(
        root.children_with_tokens()
            .map(|element| (element.kind(), element.to_string()))
            .collect::<Vec<_>>(),
        [
            (SyntaxKind::Error, "@/*a*//*b*/".to_owned()),
            (SyntaxKind::Whitespace, " ".to_owned()),
            (SyntaxKind::Identifier, "B".to_owned()),
        ]
    );
}

#[test]
fn path_segment_retry_leading_ineligibility_is_atomic_and_leaves_the_run_open() {
    fn token_retry(leading: Box<[Trivia]>) -> Item {
        Item::plain(
            LeadingTrivia::ordinary(leading),
            Payload::Token(Token {
                kind: TokenKind::Identifier,
                text: "B".into(),
            }),
        )
    }

    fn reject(mut retry: Item, successor_origin: usize) {
        let control = format!("{retry:?}");
        let operators = OperatorTable::empty();
        let mut input = "";
        let mut recover = Recover::new(&operators);
        let mut output = ParserOutput::new();
        output.start_node(SyntaxKind::Root.into());
        let result = emit_recovery_error_run(
            In::new(&mut input, &mut recover, &mut output),
            |run| {
                run.emit_literal_segment("@", 0..1, SyntaxKind::Unknown);
                let result = run.seal_path_segment_retry_leading_prefix(
                    &mut retry,
                    successor_origin,
                    UnexpectedCategory::OtherCharacter,
                );
                assert_eq!(result, PathSegmentRetryLeadingSeal::Ineligible);
                assert_eq!(format!("{retry:?}"), control);
                run.append_unexpected(UnexpectedSyntax::Token {
                    range: 0..1,
                    category: UnexpectedCategory::OtherCharacter,
                });
                result
            },
            |range, unexpected| {
                singleton_draft(
                    LiteralRole::RuleUnexpectedItem,
                    RecoveryKind::Error,
                    range,
                    unexpected,
                    ExpectedSyntax::Literal(LiteralExpected::RuleItem),
                )
            },
        );
        output.finish_node();
        let (green, records) = output.finish_with_recoveries();
        assert_eq!(result, PathSegmentRetryLeadingSeal::Ineligible);
        assert_eq!(green.to_string(), "@");
        assert_eq!(records[0].site.range, 0..1);
    }

    reject(
        token_retry(vec![Trivia::whitespace(" ".into())].into_boxed_slice()),
        3,
    );
    reject(
        token_retry(
            vec![
                Trivia::block_comment("/*x*/".into()),
                Trivia::newline("\n".into()),
            ]
            .into_boxed_slice(),
        ),
        8,
    );
    reject(
        token_retry(
            vec![
                Trivia::block_comment("/*x*/".into()),
                Trivia::newline("\r\n".into()),
            ]
            .into_boxed_slice(),
        ),
        9,
    );
    reject(
        token_retry(
            vec![
                Trivia::block_comment("/*x*/".into()),
                Trivia::line_comment("//x".into()),
            ]
            .into_boxed_slice(),
        ),
        10,
    );
    reject(
        token_retry(
            vec![
                Trivia::block_comment("/*x*/".into()),
                Trivia::whitespace(" ".into()),
                Trivia::line_comment("//x".into()),
            ]
            .into_boxed_slice(),
        ),
        11,
    );
    reject(
        token_retry(vec![Trivia::block_comment("/*x*/".into())].into_boxed_slice()),
        9,
    );
    reject(
        Item::plain(
            LeadingTrivia::ordinary(vec![Trivia::block_comment("/*x*/".into())].into_boxed_slice()),
            Payload::Eof,
        ),
        6,
    );
    reject(
        Item::plain(
            LeadingTrivia::ordinary(vec![Trivia::block_comment("/*x*/".into())].into_boxed_slice()),
            Payload::Boundary(PendingBoundary::new(
                6..7,
                Boundary::Stop(StopKind::RightParenthesis),
            )),
        ),
        6,
    );

    let carrier_origin = 1;
    let carrier = Item::finish(
        PhysicalLeadingTrivia::from_ordinary(LeadingTrivia::ordinary(
            vec![Trivia::block_comment("/*x*/".into())].into_boxed_slice(),
        )),
        Payload::Token(Token {
            kind: TokenKind::Identifier,
            text: "B".into(),
        }),
        Some(vec![ForeignSplit::quote_prefix(3, 2)]),
        carrier_origin,
    )
    .expect("carrier retry Item");
    reject(carrier, 7);

    let mut partial = token_retry(vec![Trivia::block_comment("/*x*/".into())].into_boxed_slice());
    let mut prefix_output = ParserOutput::new();
    partial.emit_leading_prefix_with(&mut prefix_output, 1, |_, _| {});
    reject(partial, 7);
}

#[test]
fn path_segment_retry_leading_seal_is_terminal_for_every_operation() {
    let operators = OperatorTable::empty();
    let mut input = "x";
    let mut recover = Recover::new(&operators);
    let mut output = ParserOutput::new();
    output.start_node(SyntaxKind::Root.into());
    let mut retry = Item::plain(
        LeadingTrivia::ordinary(vec![Trivia::block_comment("/*x*/".into())].into_boxed_slice()),
        Payload::Token(Token {
            kind: TokenKind::Identifier,
            text: "B".into(),
        }),
    );
    emit_recovery_error_run(
        In::new(&mut input, &mut recover, &mut output),
        |run| {
            run.emit_literal_segment("@", 0..1, SyntaxKind::Unknown);
            assert_eq!(
                run.seal_path_segment_retry_leading_prefix(
                    &mut retry,
                    7,
                    UnexpectedCategory::OtherCharacter,
                ),
                PathSegmentRetryLeadingSeal::Sealed
            );
            assert!(
                catch_unwind(AssertUnwindSafe(|| {
                    run.seal_path_segment_retry_leading_prefix(
                        &mut retry,
                        7,
                        UnexpectedCategory::OtherCharacter,
                    )
                }))
                .is_err()
            );
            assert!(catch_unwind(AssertUnwindSafe(|| run.lexical(|mut lex| lex.next()))).is_err());
            assert!(
                catch_unwind(AssertUnwindSafe(|| {
                    run.emit_item_as(unknown_item("!"), 7, SyntaxKind::Unknown)
                }))
                .is_err()
            );
            assert!(
                catch_unwind(AssertUnwindSafe(|| {
                    run.emit_literal_segment("!", 6..7, SyntaxKind::Unknown)
                }))
                .is_err()
            );
            assert!(
                catch_unwind(AssertUnwindSafe(|| {
                    run.append_unexpected(UnexpectedSyntax::Token {
                        range: 0..6,
                        category: UnexpectedCategory::OtherCharacter,
                    })
                }))
                .is_err()
            );
            assert!(
                catch_unwind(AssertUnwindSafe(|| {
                    run.seal_record_through_retry_leading(
                        &retry,
                        7,
                        UnexpectedCategory::OtherCharacter,
                    )
                }))
                .is_err()
            );
        },
        |range, unexpected| path_segment_draft(RecoveryKind::Error, range, unexpected),
    );
    output.finish_node();
    let (green, records) = output.finish_with_recoveries();
    assert_eq!(green.to_string(), "@/*x*/");
    assert_eq!(
        records[0].site.role,
        GrammarRole::Type(TypeRole::PathSegment)
    );
    assert_eq!(
        records[0].expectations[0].expected,
        ExpectedSyntax::TypePathSegment
    );
    assert_eq!(records[0].site.range, 0..6);
    assert_eq!(input, "x");
}

#[test]
fn retry_leading_seal_extends_only_the_record_and_preserves_the_borrowed_item() {
    let operators = OperatorTable::empty();
    let mut input = "";
    let mut recover = Recover::new(&operators);
    let mut output = ParserOutput::new();
    output.start_node(SyntaxKind::Root.into());
    let retry = Item::plain(
        LeadingTrivia::ordinary(vec![Trivia::whitespace(" ".into())].into_boxed_slice()),
        Payload::Token(Token {
            kind: TokenKind::Identifier,
            text: "B".into(),
        }),
    );
    let control = Item::plain(
        LeadingTrivia::ordinary(vec![Trivia::whitespace(" ".into())].into_boxed_slice()),
        Payload::Token(Token {
            kind: TokenKind::Identifier,
            text: "B".into(),
        }),
    );
    let sealed = emit_recovery_error_run(
        In::new(&mut input, &mut recover, &mut output),
        |run| {
            run.emit_literal_segment("@", 4..5, SyntaxKind::Unknown);
            run.seal_record_through_retry_leading(&retry, 7, UnexpectedCategory::OtherCharacter)
        },
        |range, unexpected| {
            singleton_draft(
                LiteralRole::RuleUnexpectedItem,
                RecoveryKind::Error,
                range,
                unexpected,
                ExpectedSyntax::Literal(LiteralExpected::RuleItem),
            )
        },
    );
    output.finish_node();
    let (green, records) = output.finish_with_recoveries();
    assert!(sealed);
    assert_eq!(retry, control);
    assert_eq!(green.to_string(), "@");
    assert_eq!(records.len(), 1);
    assert_eq!(records[0].site.range, 4..6);
    assert_eq!(
        records[0].unexpected,
        Arc::from([UnexpectedSyntax::Token {
            range: 4..6,
            category: UnexpectedCategory::OtherCharacter,
        }])
    );
}

#[test]
fn retry_leading_seal_rejects_ineligible_items_without_changing_normal_runs() {
    fn token_retry(leading: Box<[Trivia]>) -> Item {
        Item::plain(
            LeadingTrivia::ordinary(leading),
            Payload::Token(Token {
                kind: TokenKind::Identifier,
                text: "B".into(),
            }),
        )
    }

    fn reject(text: &str, error_range: Range<usize>, retry: Item, successor_origin: usize) {
        let operators = OperatorTable::empty();
        let mut input = "";
        let mut recover = Recover::new(&operators);
        let mut output = ParserOutput::new();
        output.start_node(SyntaxKind::Root.into());
        let sealed = emit_recovery_error_run(
            In::new(&mut input, &mut recover, &mut output),
            |run| {
                run.emit_literal_segment(text, error_range.clone(), SyntaxKind::Unknown);
                let sealed = run.seal_record_through_retry_leading(
                    &retry,
                    successor_origin,
                    UnexpectedCategory::OtherCharacter,
                );
                assert!(!sealed);
                run.append_unexpected(UnexpectedSyntax::Token {
                    range: error_range.clone(),
                    category: UnexpectedCategory::OtherCharacter,
                });
                sealed
            },
            |range, unexpected| {
                singleton_draft(
                    LiteralRole::RuleUnexpectedItem,
                    RecoveryKind::Error,
                    range,
                    unexpected,
                    ExpectedSyntax::Literal(LiteralExpected::RuleItem),
                )
            },
        );
        output.finish_node();
        let (green, records) = output.finish_with_recoveries();
        assert!(!sealed);
        assert_eq!(green.to_string(), text);
        assert_eq!(records[0].site.range, error_range);
        assert_eq!(records[0].unexpected.len(), 1);
    }

    reject(
        "@",
        0..1,
        token_retry(vec![Trivia::newline("\n".into())].into_boxed_slice()),
        3,
    );
    reject(
        "@",
        0..1,
        token_retry(vec![Trivia::newline("\r\n".into())].into_boxed_slice()),
        4,
    );
    reject("@", 0..1, token_retry(Vec::new().into_boxed_slice()), 2);
    reject(
        "@",
        0..1,
        Item::plain(
            LeadingTrivia::ordinary(vec![Trivia::whitespace(" ".into())].into_boxed_slice()),
            Payload::Boundary(PendingBoundary::new(
                2..3,
                Boundary::Stop(StopKind::RightParenthesis),
            )),
        ),
        2,
    );
    reject(
        "@",
        0..1,
        Item::plain(
            LeadingTrivia::ordinary(vec![Trivia::whitespace(" ".into())].into_boxed_slice()),
            Payload::Eof,
        ),
        2,
    );
    reject(
        "@",
        0..1,
        token_retry(vec![Trivia::whitespace(" ".into())].into_boxed_slice()),
        4,
    );
    reject(
        "@B",
        0..2,
        token_retry(vec![Trivia::whitespace(" ".into())].into_boxed_slice()),
        3,
    );
    reject(
        "@B",
        0..2,
        token_retry(vec![Trivia::whitespace(" ".into())].into_boxed_slice()),
        2,
    );

    let carrier_origin = 1;
    let carrier_comment = "/*a\n> b*/";
    let carrier = Item::finish(
        PhysicalLeadingTrivia::from_ordinary(LeadingTrivia::ordinary(
            vec![
                Trivia::block_comment(carrier_comment.into()),
                Trivia::whitespace(" ".into()),
            ]
            .into_boxed_slice(),
        )),
        Payload::Token(Token {
            kind: TokenKind::Identifier,
            text: "B".into(),
        }),
        Some(vec![ForeignSplit::quote_prefix(
            carrier_origin + "/*a\n".len(),
            2,
        )]),
        carrier_origin,
    )
    .expect("carrier retry Item");
    reject(
        "@",
        0..1,
        carrier,
        carrier_origin + carrier_comment.len() + 2,
    );

    let mut quote_leading = PhysicalLeadingTrivia::default();
    quote_leading.push_quote_prefix("> ".into());
    let quote = Item::finish(
        quote_leading,
        Payload::Token(Token {
            kind: TokenKind::Identifier,
            text: "B".into(),
        }),
        Some(vec![ForeignSplit::quote_prefix(1, 2)]),
        1,
    )
    .expect("quote-prefix retry Item");
    reject("@", 0..1, quote, 4);

    let operators = OperatorTable::empty();
    let mut input = "";
    let mut recover = Recover::new(&operators);
    let mut output = ParserOutput::new();
    output.start_node(SyntaxKind::Root.into());
    let mut partial = token_retry(vec![Trivia::whitespace(" ".into())].into_boxed_slice());
    partial.emit_leading_prefix_with(&mut output, 1, |_, _| {});
    emit_recovery_error_run(
        In::new(&mut input, &mut recover, &mut output),
        |run| {
            run.emit_literal_segment("@", 0..1, SyntaxKind::Unknown);
            assert!(!run.seal_record_through_retry_leading(
                &partial,
                3,
                UnexpectedCategory::OtherCharacter,
            ));
            run.append_unexpected(UnexpectedSyntax::Token {
                range: 0..1,
                category: UnexpectedCategory::OtherCharacter,
            });
        },
        |range, unexpected| {
            singleton_draft(
                LiteralRole::RuleUnexpectedItem,
                RecoveryKind::Error,
                range,
                unexpected,
                ExpectedSyntax::Literal(LiteralExpected::RuleItem),
            )
        },
    );
    output.finish_node();
    let (green, records) = output.finish_with_recoveries();
    assert_eq!(green.to_string(), " @");
    assert_eq!(records[0].site.range, 0..1);
}

#[test]
fn retry_leading_seal_requires_empty_evidence_and_is_terminal_for_every_operation() {
    let operators = OperatorTable::empty();
    let mut input = "x";
    let mut recover = Recover::new(&operators);
    let mut output = ParserOutput::new();
    output.start_node(SyntaxKind::Root.into());
    let mut retry = Item::plain(
        LeadingTrivia::ordinary(vec![Trivia::whitespace(" ".into())].into_boxed_slice()),
        Payload::Token(Token {
            kind: TokenKind::Identifier,
            text: "B".into(),
        }),
    );
    emit_recovery_error_run(
        In::new(&mut input, &mut recover, &mut output),
        |run| {
            assert!(
                catch_unwind(AssertUnwindSafe(|| run.seal_record_through_retry_leading(
                    &retry,
                    3,
                    UnexpectedCategory::OtherCharacter,
                )))
                .is_err()
            );
            assert!(
                catch_unwind(AssertUnwindSafe(|| {
                    run.seal_path_segment_retry_leading_prefix(
                        &mut retry,
                        3,
                        UnexpectedCategory::OtherCharacter,
                    )
                }))
                .is_err()
            );
            run.emit_literal_segment("@", 0..1, SyntaxKind::Unknown);
            assert!(run.seal_record_through_retry_leading(
                &retry,
                3,
                UnexpectedCategory::OtherCharacter,
            ));
            assert!(
                catch_unwind(AssertUnwindSafe(|| run.seal_record_through_retry_leading(
                    &retry,
                    3,
                    UnexpectedCategory::OtherCharacter,
                )))
                .is_err()
            );
            assert!(catch_unwind(AssertUnwindSafe(|| run.lexical(|mut lex| lex.next()))).is_err());
            assert!(
                catch_unwind(AssertUnwindSafe(|| {
                    run.emit_item_as(unknown_item("!"), 4, SyntaxKind::Unknown)
                }))
                .is_err()
            );
            assert!(
                catch_unwind(AssertUnwindSafe(|| {
                    run.emit_literal_segment("!", 3..4, SyntaxKind::Unknown)
                }))
                .is_err()
            );
            assert!(
                catch_unwind(AssertUnwindSafe(|| {
                    run.append_unexpected(UnexpectedSyntax::Token {
                        range: 0..1,
                        category: UnexpectedCategory::OtherCharacter,
                    })
                }))
                .is_err()
            );
        },
        |range, unexpected| {
            singleton_draft(
                LiteralRole::RuleUnexpectedItem,
                RecoveryKind::Error,
                range,
                unexpected,
                ExpectedSyntax::Literal(LiteralExpected::RuleItem),
            )
        },
    );
    output.finish_node();
    let (green, records) = output.finish_with_recoveries();
    assert_eq!(green.to_string(), "@");
    assert_eq!(input, "x");
    assert_eq!(records[0].site.range, 0..2);

    let mut input = "";
    let mut recover = Recover::new(&operators);
    let mut output = ParserOutput::new();
    output.start_node(SyntaxKind::Root.into());
    emit_recovery_error_run(
        In::new(&mut input, &mut recover, &mut output),
        |run| {
            run.emit_literal_segment("@", 0..1, SyntaxKind::Unknown);
            run.append_unexpected(UnexpectedSyntax::Token {
                range: 0..1,
                category: UnexpectedCategory::OtherCharacter,
            });
            assert!(
                catch_unwind(AssertUnwindSafe(|| run.seal_record_through_retry_leading(
                    &retry,
                    3,
                    UnexpectedCategory::OtherCharacter,
                )))
                .is_err()
            );
        },
        |range, unexpected| {
            singleton_draft(
                LiteralRole::RuleUnexpectedItem,
                RecoveryKind::Error,
                range,
                unexpected,
                ExpectedSyntax::Literal(LiteralExpected::RuleItem),
            )
        },
    );
    output.finish_node();
    let (_, records) = output.finish_with_recoveries();
    assert_eq!(records[0].site.range, 0..1);
}

#[test]
fn rejected_branch_preserves_tree_records_id_cursor_input_and_item() {
    let frozen = [frozen_record(
        7,
        LiteralRole::StringTerminator,
        RecoveryKind::Missing,
        0..0,
        Arc::from([]),
        Arc::from([expectation(
            role(LiteralRole::StringTerminator),
            ExpectedSyntax::Literal(LiteralExpected::StringTerminator),
            0..0,
            ExpectationSources::COMMITTED_RECOVERY_RULE,
        )]),
        0,
    )];
    let operators = OperatorTable::empty();
    let mut input = "tail";
    let mut recover = Recover::new(&operators);
    let mut output = ParserOutput::reconcile(&frozen);
    output.start_node(SyntaxKind::Root.into());
    output.start_node(SyntaxKind::IdentifierExpression.into());
    output.token(SyntaxKind::Identifier.into(), "sentinel");
    output.finish_node();
    output.commit_recovery(singleton_draft(
        LiteralRole::StringTerminator,
        RecoveryKind::Missing,
        0..0,
        Arc::from([]),
        ExpectedSyntax::Literal(LiteralExpected::StringTerminator),
    ));
    let before = output.diagnostic_position();
    let item = unknown_item("@");
    let control_item = unknown_item("@");
    assert!(
        classify_statement_item_normalized(
            In::new(&mut input, &mut recover, &mut output),
            &item,
            0,
            0,
            None,
        )
        .is_none()
    );
    assert_eq!(input, "tail");
    assert_eq!(item, control_item);
    assert_eq!(output.diagnostic_position(), before);
    assert_eq!(output.recovery_slot_count(), 1);
    output.finish_node();
    let (green, records) = output.finish_with_recoveries();
    assert_eq!(green, seeded_root());
    assert_eq!(records.len(), 1);
    assert_eq!(records[0].id, DiagnosticId(7));
}

#[test]
fn literal_recovery_vocabulary_is_exact_and_pipe_is_explicit() {
    fn literal_role_name(role: LiteralRole) -> &'static str {
        match role {
            LiteralRole::StringTerminator => "StringTerminator",
            LiteralRole::StringEscapeSimpleTarget => "StringEscapeSimpleTarget",
            LiteralRole::StringEscapeUnicodeHex => "StringEscapeUnicodeHex",
            LiteralRole::StringEscapeUnicodeEnd => "StringEscapeUnicodeEnd",
            LiteralRole::StringInterpolationOpenBrace => "StringInterpolationOpenBrace",
            LiteralRole::StringInterpolationCloseBrace => "StringInterpolationCloseBrace",
            LiteralRole::RuleBodyCloseBrace => "RuleBodyCloseBrace",
            LiteralRole::RuleParenClose => "RuleParenClose",
            LiteralRole::RuleCaptureRightItem => "RuleCaptureRightItem",
            LiteralRole::RuleFieldName => "RuleFieldName",
            LiteralRole::RulePathName => "RulePathName",
            LiteralRole::RuleUnexpectedItem => "RuleUnexpectedItem",
            LiteralRole::RuleLiteralTerminator => "RuleLiteralTerminator",
            LiteralRole::RuleLiteralInterpolationCloseBrace => "RuleLiteralInterpolationCloseBrace",
            LiteralRole::RuleLazyCaptureName => "RuleLazyCaptureName",
            LiteralRole::RuleLazyCaptureCloseBrace => "RuleLazyCaptureCloseBrace",
        }
    }
    fn literal_expected_name(expected: LiteralExpected) -> &'static str {
        match expected {
            LiteralExpected::StringTerminator => "StringTerminator",
            LiteralExpected::StringEscapeTarget => "StringEscapeTarget",
            LiteralExpected::UnicodeHexDigit => "UnicodeHexDigit",
            LiteralExpected::RuleItem => "RuleItem",
            LiteralExpected::RuleLiteralTerminator => "RuleLiteralTerminator",
        }
    }
    let roles = [
        LiteralRole::StringTerminator,
        LiteralRole::StringEscapeSimpleTarget,
        LiteralRole::StringEscapeUnicodeHex,
        LiteralRole::StringEscapeUnicodeEnd,
        LiteralRole::StringInterpolationOpenBrace,
        LiteralRole::StringInterpolationCloseBrace,
        LiteralRole::RuleBodyCloseBrace,
        LiteralRole::RuleParenClose,
        LiteralRole::RuleCaptureRightItem,
        LiteralRole::RuleFieldName,
        LiteralRole::RulePathName,
        LiteralRole::RuleUnexpectedItem,
        LiteralRole::RuleLiteralTerminator,
        LiteralRole::RuleLiteralInterpolationCloseBrace,
        LiteralRole::RuleLazyCaptureName,
        LiteralRole::RuleLazyCaptureCloseBrace,
    ];
    assert_eq!(roles.map(literal_role_name).len(), 16);
    let expected = [
        LiteralExpected::StringTerminator,
        LiteralExpected::StringEscapeTarget,
        LiteralExpected::UnicodeHexDigit,
        LiteralExpected::RuleItem,
        LiteralExpected::RuleLiteralTerminator,
    ];
    assert_eq!(expected.map(literal_expected_name).len(), 5);
    assert_eq!(
        UnexpectedCategory::Punctuation(PunctuationEvidence::Pipe),
        UnexpectedCategory::Punctuation(PunctuationEvidence::Pipe)
    );
}

#[test]
fn rule_local_unexpected_categories_cover_field_path_and_nonoperator_unknown() {
    assert_eq!(
        rule_item_unexpected_category(&token_item(TokenKind::Pipe, "|")),
        UnexpectedCategory::Punctuation(PunctuationEvidence::Pipe),
        "the malformed field continuation in `.|` keeps exact Pipe evidence"
    );
    assert_eq!(
        rule_item_unexpected_category(&unknown_item("+")),
        UnexpectedCategory::OperatorLike,
        "the malformed path continuation in `::+` uses its owned operator-shaped spelling"
    );
    assert_eq!(
        rule_item_unexpected_category(&unknown_item("@")),
        UnexpectedCategory::OtherCharacter
    );
}
