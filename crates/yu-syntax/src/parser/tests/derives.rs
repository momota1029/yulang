use reborrow_generic::Reborrow as _;
use std::sync::Arc;

use super::*;
use crate::parser::{
    current_item::{CurrentItem, current_item},
    derives::derives_clause_normalized,
    driver::{advanced_origin, suffix_marker},
    lexer::scan_type_nud_payload,
    statement::StatementLineHandoff,
    type_expr::TypeOuterBoundary,
    yumark::{FenceOpener, FencePrefixPolicy},
};
use crate::session::{
    DeclarationRole, DerivesRole, DiagnosticId, ExpectationSources, ExpectedSyntax, GrammarRole,
    RecoveryKind, RecoverySiteKey, SyntaxExpectation, TypeRole, UnexpectedCategory,
    UnexpectedSyntax,
};

#[derive(Clone, Copy)]
enum RecoveryHandling<'a> {
    Reject,
    Retain,
    Frozen(&'a [CommittedRecoveryRecord]),
    Seeded(Option<&'a [CommittedRecoveryRecord]>),
}

fn active_fence() -> FenceBoundary {
    FenceBoundary {
        opener: FenceOpener {
            line: 0,
            marker: 0..3,
            marker_width: 3,
        },
        prefix_policy: FencePrefixPolicy::ActivePrefixQuote { depth: 2, base: 0 },
        close_column: 0,
    }
}

#[allow(clippy::too_many_arguments)]
fn run_derives_normalized<'source>(
    source: &'source str,
    operators: &OperatorTable,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    line_handoff: StatementLineHandoff,
    role_boundary: TypeOuterBoundary,
    recovery_handling: RecoveryHandling<'_>,
) -> (
    GreenNode,
    Item,
    usize,
    LineEntry,
    &'source str,
    Vec<CommittedRecoveryRecord>,
) {
    run_derives_with_stops(
        source,
        operators,
        item_origin,
        line_entry,
        fence,
        line_handoff,
        role_boundary,
        recovery_handling,
        0,
    )
}

#[allow(clippy::too_many_arguments)]
fn run_derives_with_stops<'source>(
    source: &'source str,
    operators: &OperatorTable,
    item_origin: usize,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
    line_handoff: StatementLineHandoff,
    role_boundary: TypeOuterBoundary,
    recovery_handling: RecoveryHandling<'_>,
    stops: Stops,
) -> (
    GreenNode,
    Item,
    usize,
    LineEntry,
    &'source str,
    Vec<CommittedRecoveryRecord>,
) {
    let mut input = source;
    let mut recover = Recover::new(operators);
    let mut builder = match recovery_handling {
        RecoveryHandling::Frozen(records) | RecoveryHandling::Seeded(Some(records)) => {
            GreenNodeBuilder::reconcile(records)
        }
        _ => GreenNodeBuilder::new(),
    };
    builder.start_node(SyntaxKind::Root.into());
    if matches!(recovery_handling, RecoveryHandling::Seeded(_)) {
        let seed = derives_record(DerivesRole::ViaTarget, RecoveryKind::Missing, 0..0, 0);
        builder.start_node(SyntaxKind::Missing.into());
        builder.finish_node();
        builder.commit_recovery(crate::parser::output::RecoveryDraft::new(
            seed.site,
            seed.kind,
            seed.unexpected,
            seed.expectations,
            seed.primary_expectation,
        ));
    }
    let (pending, item_origin, line_entry) = {
        let mut i = In::new(&mut input, &mut recover, &mut builder);
        let entry = suffix_marker(i.rb());
        let CurrentItem {
            item: keyword,
            next_line_entry,
        } = i
            .token(|lex| {
                current_item(
                    lex,
                    item_origin,
                    line_entry,
                    fence,
                    |lex, leading, origin, fence, _| {
                        scan_type_nud_payload(lex, leading, origin, fence)
                    },
                )
            })
            .expect("a direct Derives harness starts with one current Item");
        assert_eq!(keyword.payload_view().spelling(), Some("derives"));
        let item_origin = advanced_origin(item_origin, entry, i.rb());
        derives_clause_normalized(
            i,
            keyword,
            0,
            stops,
            line_handoff,
            role_boundary,
            item_origin,
            next_line_entry,
            fence,
            Some(crate::parser::ambient_claim::AmbientClaimView::root_statement(0)).into(),
        )
    };
    builder.finish_node();
    let (green, recoveries) = match recovery_handling {
        RecoveryHandling::Reject => (builder.finish(), Vec::new()),
        _ => builder.finish_with_recoveries(),
    };
    (green, pending, item_origin, line_entry, input, recoveries)
}

fn required_type_primary_error_record() -> CommittedRecoveryRecord {
    let role = GrammarRole::Type(TypeRole::Primary);
    let range = 6211..6213;
    CommittedRecoveryRecord {
        id: DiagnosticId(0),
        site: RecoverySiteKey {
            role,
            range: range.clone(),
        },
        kind: RecoveryKind::Error,
        unexpected: Arc::from([UnexpectedSyntax::Token {
            range: range.clone(),
            category: UnexpectedCategory::OtherCharacter,
        }]),
        expectations: Arc::from([SyntaxExpectation {
            role,
            expected: ExpectedSyntax::TypeExpression,
            range,
            sources: ExpectationSources::COMMITTED_RECOVERY_RULE,
        }]),
        primary_expectation: 0,
    }
}

fn derives_record(
    role: DerivesRole,
    kind: RecoveryKind,
    range: std::ops::Range<usize>,
    id: u32,
) -> CommittedRecoveryRecord {
    let expected = match role {
        DerivesRole::RoleReference => ExpectedSyntax::TypeExpression,
        DerivesRole::ViaTarget => ExpectedSyntax::Identifier,
    };
    let role = GrammarRole::Declaration(DeclarationRole::Derives(role));
    CommittedRecoveryRecord {
        id: DiagnosticId(id),
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
            expected,
            range,
            sources: ExpectationSources::COMMITTED_RECOVERY_RULE,
        }]),
        primary_expectation: 0,
    }
}

fn header_role_boundary() -> TypeOuterBoundary {
    TypeOuterBoundary::DERIVES
        .with(TypeOuterBoundary::VIA)
        .with(TypeOuterBoundary::WITH)
        .with(TypeOuterBoundary::IMPL)
        .with(TypeOuterBoundary::EQUALS)
}

fn count(green: &GreenNode, kind: SyntaxKind) -> usize {
    SyntaxNode::new_root(green.clone())
        .descendants()
        .filter(|node| node.kind() == kind)
        .count()
}

fn token_count(green: &GreenNode, kind: SyntaxKind) -> usize {
    SyntaxNode::new_root(green.clone())
        .descendants_with_tokens()
        .filter_map(|element| element.into_token())
        .filter(|token| token.kind() == kind)
        .count()
}

#[test]
fn derives_normalized_streams_crlf_prefixes_comma_and_raw_via() {
    let fence = active_fence();
    let operators = OperatorTable::from_declarations([OperatorDeclaration::new(
        "key",
        OperatorFixities::new().with_nullfix(),
    )])
    .expect("dynamic word operator table");
    let origin = 6100;
    let accepted = "> > derives Eq,\r\n> >   Debug via key";
    let source = format!("{accepted}\r\n> > ```\r\nouter");
    let (green, boundary, actual_origin, line_entry, remainder, _) = run_derives_normalized(
        &source,
        &operators,
        origin,
        LineEntry::PhysicalStart,
        Some(&fence),
        StatementLineHandoff::OrdinaryLayout,
        header_role_boundary(),
        RecoveryHandling::Reject,
    );
    assert_eq!(green.to_string(), accepted);
    assert_eq!(remainder, "> > ```\r\nouter");
    assert_eq!(actual_origin, origin + accepted.len() + 2);
    assert_eq!(line_entry, LineEntry::PhysicalStart);
    assert_eq!(count(&green, SyntaxKind::DerivesClause), 1);
    assert_eq!(count(&green, SyntaxKind::TypeExpression), 2);
    assert_eq!(token_count(&green, SyntaxKind::ViaKw), 1);
    assert_eq!(token_count(&green, SyntaxKind::YmQuotePrefix), 2);
    assert_eq!(token_count(&green, SyntaxKind::NullfixOperatorUse), 0);
    let (leading, pending) = emit_terminal_leading_text(boundary);
    assert_eq!(leading, "\r\n");
    assert_eq!(pending.coordinate(), actual_origin);
}

#[test]
fn derives_normalized_recovers_role_and_via_slots_before_the_fence() {
    let fence = active_fence();
    let operators = OperatorTable::empty();
    for (accepted, missing, errors, expected_recoveries) in [
        (
            "> > derives",
            1,
            0,
            vec![derives_record(
                DerivesRole::RoleReference,
                RecoveryKind::Missing,
                6212..6212,
                0,
            )],
        ),
        (
            "> > derives Eq, via",
            2,
            0,
            vec![
                {
                    let role = GrammarRole::Declaration(crate::session::DeclarationRole::Derives(
                        crate::session::DerivesRole::RoleReference,
                    ));
                    CommittedRecoveryRecord {
                        id: DiagnosticId(0),
                        site: RecoverySiteKey {
                            role,
                            range: 6215..6215,
                        },
                        kind: RecoveryKind::Missing,
                        unexpected: Arc::from([]),
                        expectations: Arc::from([SyntaxExpectation {
                            role,
                            expected: ExpectedSyntax::TypeExpression,
                            range: 6215..6215,
                            sources: ExpectationSources::COMMITTED_RECOVERY_RULE,
                        }]),
                        primary_expectation: 0,
                    }
                },
                derives_record(DerivesRole::ViaTarget, RecoveryKind::Missing, 6220..6220, 1),
            ],
        ),
        (
            "> > derives @ Role via @ target",
            0,
            2,
            vec![
                required_type_primary_error_record(),
                derives_record(DerivesRole::ViaTarget, RecoveryKind::Error, 6222..6224, 1),
            ],
        ),
    ] {
        let source = format!("{accepted}\n> > ```\nouter");
        let (green, boundary, item_origin, line_entry, remainder, recoveries) =
            run_derives_normalized(
                &source,
                &operators,
                6200,
                LineEntry::PhysicalStart,
                Some(&fence),
                StatementLineHandoff::OrdinaryLayout,
                header_role_boundary(),
                RecoveryHandling::Retain,
            );
        assert_eq!(green.to_string(), accepted, "{accepted:?}");
        assert_eq!(remainder, "> > ```\nouter", "{accepted:?}");
        assert_eq!(line_entry, LineEntry::PhysicalStart, "{accepted:?}");
        assert_eq!(count(&green, SyntaxKind::Missing), missing, "{accepted:?}");
        assert_eq!(count(&green, SyntaxKind::Error), errors, "{accepted:?}");
        assert_eq!(recoveries, expected_recoveries, "{accepted:?}");
        let (leading, pending) = emit_terminal_leading_text(boundary);
        assert_eq!(leading, "\n", "{accepted:?}");
        assert_eq!(pending.coordinate(), item_origin, "{accepted:?}");
    }
}

#[test]
fn derives_normalized_hands_exact_outer_successors_and_terminals_up() {
    let fence = active_fence();
    let operators = OperatorTable::empty();
    for (word, remainder) in [("with", " tail"), ("impl", " P"), ("=", " Body")] {
        let source = format!("> > derives Eq {word}{remainder}");
        let (green, mut pending, item_origin, line_entry, actual_remainder, _) =
            run_derives_normalized(
                &source,
                &operators,
                6300,
                LineEntry::PhysicalStart,
                Some(&fence),
                StatementLineHandoff::OrdinaryLayout,
                header_role_boundary(),
                RecoveryHandling::Reject,
            );
        assert_eq!(green.to_string(), "> > derives Eq", "{word:?}");
        assert_eq!(pending.payload_view().spelling(), Some(word), "{word:?}");
        assert_eq!(actual_remainder, remainder, "{word:?}");
        assert_eq!(line_entry, LineEntry::InLine, "{word:?}");
        assert_eq!(
            item_origin,
            6300 + source.len() - remainder.len(),
            "{word:?}"
        );
        assert_eq!(emit_pending_leading_text(&mut pending), " ", "{word:?}");
    }

    for (source, expected_remainder, expected_entry, expected_leading) in [
        (
            "> > derives Eq\r\n> ]\r\nouter",
            "> ]\r\nouter",
            LineEntry::PhysicalStart,
            "\r\n",
        ),
        ("> > derives Eq", "", LineEntry::InLine, ""),
    ] {
        let (green, boundary, item_origin, line_entry, remainder, _) = run_derives_normalized(
            source,
            &operators,
            6350,
            LineEntry::PhysicalStart,
            Some(&fence),
            StatementLineHandoff::OrdinaryLayout,
            header_role_boundary(),
            RecoveryHandling::Reject,
        );
        assert_eq!(green.to_string(), "> > derives Eq", "{source:?}");
        assert_eq!(remainder, expected_remainder, "{source:?}");
        assert_eq!(line_entry, expected_entry, "{source:?}");
        let (leading, pending) = emit_terminal_leading_text(boundary);
        assert_eq!(leading, expected_leading, "{source:?}");
        assert_eq!(pending.coordinate(), item_origin, "{source:?}");
    }
}

#[test]
fn derives_normalized_keeps_line_handoffs_and_nested_boundaries_distinct() {
    let operators = OperatorTable::empty();
    for (handoff, gap) in [
        (StatementLineHandoff::OrdinaryLayout, "\n"),
        (StatementLineHandoff::BracedStatementSequence, "\n  "),
        (
            StatementLineHandoff::CatchArmSequenceThroughInlineCanonicalStatement,
            "\n  ",
        ),
        (StatementLineHandoff::CatchBracedArm, "\n  "),
    ] {
        let source = format!("derives{gap}next");
        let (green, mut pending, item_origin, line_entry, remainder, _) = run_derives_normalized(
            &source,
            &operators,
            6400,
            LineEntry::InLine,
            None,
            handoff,
            header_role_boundary(),
            RecoveryHandling::Retain,
        );
        assert_eq!(green.to_string(), "derives", "{handoff:?}");
        assert_eq!(count(&green, SyntaxKind::Missing), 1, "{handoff:?}");
        assert_eq!(
            pending.payload_view().spelling(),
            Some("next"),
            "{handoff:?}"
        );
        assert_eq!(emit_pending_leading_text(&mut pending), gap, "{handoff:?}");
        assert_eq!(item_origin, 6400 + source.len(), "{handoff:?}");
        assert_eq!(line_entry, LineEntry::InLine, "{handoff:?}");
        assert_eq!(remainder, "", "{handoff:?}");
    }

    let source = "derives (Eq via Inner) via key";
    let (green, pending, item_origin, line_entry, remainder, _) = run_derives_normalized(
        source,
        &operators,
        6500,
        LineEntry::InLine,
        None,
        StatementLineHandoff::OrdinaryLayout,
        header_role_boundary(),
        RecoveryHandling::Reject,
    );
    assert_eq!(green.to_string(), source);
    assert!(pending.payload_view().is_eof());
    assert_eq!(item_origin, 6500 + source.len());
    assert_eq!(line_entry, LineEntry::InLine);
    assert_eq!(remainder, "");
    assert_eq!(token_count(&green, SyntaxKind::ViaKw), 1);
    assert_eq!(
        SyntaxNode::new_root(green)
            .descendants_with_tokens()
            .filter_map(|element| element.into_token())
            .filter(|token| token.kind() == SyntaxKind::Identifier && token.text() == "via")
            .count(),
        1
    );
}

#[test]
fn derives_slots_publish_exact_fresh_frozen_and_seeded_records() {
    use DerivesRole::{RoleReference, ViaTarget};
    use RecoveryKind::{Error, Missing};
    let operators = OperatorTable::empty();
    for (source, role, kind, range, accepted, leading) in [
        ("derives", RoleReference, Missing, 7..7, "derives", ""),
        ("derives  ", RoleReference, Missing, 9..9, "derives", "  "),
        (
            "derives Eq,",
            RoleReference,
            Missing,
            11..11,
            "derives Eq,",
            "",
        ),
        (
            "derives Eq via",
            ViaTarget,
            Missing,
            14..14,
            "derives Eq via",
            "",
        ),
        (
            "derives Eq via  ",
            ViaTarget,
            Missing,
            16..16,
            "derives Eq via",
            "  ",
        ),
        (
            "derives Eq via ]",
            ViaTarget,
            Missing,
            14..14,
            "derives Eq via",
            " ",
        ),
        (
            "derives Eq via @ 123 target",
            ViaTarget,
            Error,
            14..20,
            "derives Eq via @ 123 target",
            "",
        ),
        (
            "derives Eq via @",
            ViaTarget,
            Error,
            14..16,
            "derives Eq via @",
            "",
        ),
    ] {
        for origin in [0, 7100] {
            let expected = derives_record(role, kind, origin + range.start..origin + range.end, 0);
            let (green, mut pending, _, _, _, records) = run_derives_normalized(
                source,
                &operators,
                origin,
                LineEntry::InLine,
                None,
                StatementLineHandoff::OrdinaryLayout,
                header_role_boundary(),
                RecoveryHandling::Retain,
            );
            assert_eq!(green.to_string(), accepted, "{source:?}");
            assert_eq!(records, [expected], "{source:?}");
            assert_eq!(
                emit_pending_leading_text(&mut pending),
                leading,
                "{source:?}"
            );
            let (again, _, _, _, _, frozen) = run_derives_normalized(
                source,
                &operators,
                origin,
                LineEntry::InLine,
                None,
                StatementLineHandoff::OrdinaryLayout,
                header_role_boundary(),
                RecoveryHandling::Frozen(&records),
            );
            assert_eq!(again, green);
            assert_eq!(frozen, records);
        }
    }
    let source = "derives Eq via @";
    let (green, _, _, _, _, records) = run_derives_normalized(
        source,
        &operators,
        100,
        LineEntry::InLine,
        None,
        StatementLineHandoff::OrdinaryLayout,
        header_role_boundary(),
        RecoveryHandling::Seeded(None),
    );
    assert_eq!(
        records,
        [
            derives_record(ViaTarget, Missing, 0..0, 0),
            derives_record(ViaTarget, Error, 114..116, 1),
        ]
    );
    let mut frozen = records;
    frozen[0].id = DiagnosticId(7);
    frozen[1].id = DiagnosticId(13);
    let (again, _, _, _, _, records) = run_derives_normalized(
        source,
        &operators,
        100,
        LineEntry::InLine,
        None,
        StatementLineHandoff::OrdinaryLayout,
        header_role_boundary(),
        RecoveryHandling::Seeded(Some(&frozen)),
    );
    assert_eq!(again, green);
    assert_eq!(records, frozen);
}

#[test]
fn derives_via_error_preserves_protected_identifier_before_retry() {
    let operators = OperatorTable::empty();
    for (gap, word, handoff) in [
        (" ", "derives", StatementLineHandoff::OrdinaryLayout),
        (" ", "via", StatementLineHandoff::OrdinaryLayout),
        (" ", "with", StatementLineHandoff::OrdinaryLayout),
        (" ", "impl", StatementLineHandoff::OrdinaryLayout),
        ("\r\n", "next", StatementLineHandoff::OrdinaryLayout),
        (
            "\r\n  ",
            "next",
            StatementLineHandoff::BracedStatementSequence,
        ),
        (
            "\r\n  ",
            "next",
            StatementLineHandoff::CatchArmSequenceThroughInlineCanonicalStatement,
        ),
        ("\r\n  ", "next", StatementLineHandoff::CatchBracedArm),
    ] {
        for origin in [0, 7200] {
            let source = format!("derives Eq via @ 123{gap}{word} tail");
            let expected = [derives_record(
                DerivesRole::ViaTarget,
                RecoveryKind::Error,
                origin + 14..origin + 20,
                0,
            )];
            for handling in [
                RecoveryHandling::Retain,
                RecoveryHandling::Frozen(&expected),
            ] {
                let (green, mut pending, successor, entry, rest, records) = run_derives_normalized(
                    &source,
                    &operators,
                    origin,
                    LineEntry::InLine,
                    None,
                    handoff,
                    header_role_boundary(),
                    handling,
                );
                assert_eq!(green.to_string(), "derives Eq via @ 123", "{source:?}");
                assert_eq!(records, expected, "{source:?}");
                assert_eq!(pending.payload_view().spelling(), Some(word));
                assert_eq!(
                    pending.extent(successor).recovery_range(),
                    origin + 20..origin + 20 + gap.len() + word.len()
                );
                assert_eq!(emit_pending_leading_text(&mut pending), gap);
                assert_eq!(successor, origin + source.len() - " tail".len());
                assert_eq!(entry, LineEntry::InLine);
                assert_eq!(rest, " tail");
                assert_eq!(count(&green, SyntaxKind::Missing), 0);
                assert_eq!(count(&green, SyntaxKind::Error), 1);
                let error = SyntaxNode::new_root(green)
                    .descendants()
                    .find(|node| node.kind() == SyntaxKind::Error)
                    .unwrap();
                assert_eq!(error.to_string(), " @ 123");
            }
        }
    }
}

#[test]
fn derives_via_error_keeps_shifted_utf8_crlf_fence_and_foreign_prefix() {
    let operators = OperatorTable::empty();
    let fence = active_fence();
    for terminal in ["> > ```\r\nouter", "> ]\r\nouter"] {
        let accepted = "> > derives 役 via @";
        let source = format!("{accepted}\r\n{terminal}");
        let start = 7300 + "> > derives 役 via".len();
        let end = 7300 + accepted.len();
        let expected = [derives_record(
            DerivesRole::ViaTarget,
            RecoveryKind::Error,
            start..end,
            0,
        )];
        for handling in [
            RecoveryHandling::Retain,
            RecoveryHandling::Frozen(&expected),
        ] {
            let (green, pending, successor, entry, rest, records) = run_derives_normalized(
                &source,
                &operators,
                7300,
                LineEntry::PhysicalStart,
                Some(&fence),
                StatementLineHandoff::OrdinaryLayout,
                header_role_boundary(),
                handling,
            );
            assert_eq!(green.to_string(), accepted);
            assert_eq!(records, expected);
            assert_eq!(rest, terminal);
            assert_eq!(entry, LineEntry::PhysicalStart);
            assert_eq!(successor, end + 2);
            let (leading, boundary) = emit_terminal_leading_text(pending);
            assert_eq!(leading, "\r\n");
            assert_eq!(boundary.coordinate(), successor);
        }
    }
}

#[test]
fn derives_via_error_preserves_active_companions() {
    use crate::parser::operator::{STOP_ELSE, STOP_ELSIF};
    let operators = OperatorTable::empty();
    for (word, stop) in [("else", STOP_ELSE), ("elsif", STOP_ELSIF)] {
        let source = format!("derives Eq via @{word}: tail");
        let expected = [derives_record(
            DerivesRole::ViaTarget,
            RecoveryKind::Error,
            8114..8116,
            0,
        )];
        for handling in [
            RecoveryHandling::Retain,
            RecoveryHandling::Frozen(&expected),
        ] {
            let (green, pending, successor, entry, rest, records) = run_derives_with_stops(
                &source,
                &operators,
                8100,
                LineEntry::InLine,
                None,
                StatementLineHandoff::OrdinaryLayout,
                header_role_boundary(),
                handling,
                stop,
            );
            assert_eq!(green.to_string(), "derives Eq via @");
            assert_eq!(records, expected);
            assert_eq!(pending.payload_view().spelling(), Some(word));
            assert_eq!(
                pending.extent(successor).recovery_range(),
                8116..8116 + word.len()
            );
            assert_eq!(entry, LineEntry::InLine);
            assert_eq!(rest, ": tail");
        }
    }
}

#[test]
fn derives_role_override_does_not_replace_entered_type_path_owner() {
    let operators = OperatorTable::empty();
    let role = GrammarRole::Type(TypeRole::PathSegment);
    let expected = [CommittedRecoveryRecord {
        id: DiagnosticId(0),
        site: RecoverySiteKey {
            role,
            range: 8212..8212,
        },
        kind: RecoveryKind::Missing,
        unexpected: Arc::from([]),
        expectations: Arc::from([SyntaxExpectation {
            role,
            expected: ExpectedSyntax::TypePathSegment,
            range: 8212..8212,
            sources: ExpectationSources::COMMITTED_RECOVERY_RULE,
        }]),
        primary_expectation: 0,
    }];
    for handling in [
        RecoveryHandling::Retain,
        RecoveryHandling::Frozen(&expected),
    ] {
        let (green, pending, successor, _, rest, records) = run_derives_normalized(
            "derives Eq::",
            &operators,
            8200,
            LineEntry::InLine,
            None,
            StatementLineHandoff::OrdinaryLayout,
            header_role_boundary(),
            handling,
        );
        assert_eq!(green.to_string(), "derives Eq::");
        assert_eq!(records, expected);
        assert!(pending.payload_view().is_eof());
        assert_eq!(successor, 8212);
        assert_eq!(rest, "");
    }
}
