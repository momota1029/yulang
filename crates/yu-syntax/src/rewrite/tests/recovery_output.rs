use std::{
    ops::Range,
    panic::{AssertUnwindSafe, catch_unwind},
    sync::Arc,
};

use chasa_recover::In;

use crate::{
    SyntaxKind, SyntaxNode,
    operator::OperatorTable,
    session::{
        CommittedRecoveryRecord, DiagnosticId, ExpectationSources, ExpectedSyntax, GrammarRole,
        LiteralExpected, LiteralRole, PunctuationEvidence, RecoveryKind, RecoverySiteKey,
        SyntaxExpectation, UnexpectedCategory, UnexpectedSyntax,
    },
};

use super::super::{
    emit::{emit_recovery_error_item, emit_recovery_error_run, emit_recovery_missing},
    item::{
        Boundary, ForeignSplit, Item, LeadingTrivia, Payload, PendingBoundary,
        PhysicalLeadingTrivia, StopKind, Token, TokenKind, Trivia,
    },
    output::{RecoveryDraft, RewriteOutput},
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

fn finish_empty_root(
    mut output: RewriteOutput<'_>,
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
    let mut output = RewriteOutput::new();
    output.start_node(SyntaxKind::Root.into());
    output.start_node(SyntaxKind::IdentifierExpression.into());
    output.token(SyntaxKind::Identifier.into(), "sentinel");
    output.finish_node();
    output.finish_node();
    output.finish()
}

#[test]
fn fresh_sequence_assigns_zero_one_and_preserves_same_offset_order_and_all_fields() {
    let mut output = RewriteOutput::new();
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
    let mut output = RewriteOutput::reconcile(&frozen);
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
    let mut output = RewriteOutput::reconcile(&frozen);
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
    assert!(output.recoveries().is_empty());

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
    assert_eq!(output.recoveries().len(), 1);
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
            RewriteOutput::reconcile(std::slice::from_ref(&valid))
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
        catch_unwind(AssertUnwindSafe(|| RewriteOutput::reconcile(
            std::slice::from_ref(&invalid)
        )))
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
    let mut output = RewriteOutput::new();
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
    let mut output = RewriteOutput::new();
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
    let mut output = RewriteOutput::new();
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
    let mut output = RewriteOutput::new();
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

    const ERROR_RUN_CAPABILITY: [&str; 4] = [
        "lexical",
        "emit_item_as",
        "emit_literal_segment",
        "append_unexpected",
    ];
    assert_eq!(ERROR_RUN_CAPABILITY.len(), 4);
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
    let mut output = RewriteOutput::reconcile(&frozen);
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
    assert_eq!(output.recoveries().len(), 1);
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
