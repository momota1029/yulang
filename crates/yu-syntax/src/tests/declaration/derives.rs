use std::sync::Arc;

use crate::recovery_record::{
    DeclarationRole, DerivesRole, DiagnosticId, ExpectationSources, ExpectedSyntax, GrammarRole,
    RecoveryKind, RecoverySiteKey, SyntaxExpectation, TypeRole, UnexpectedCategory,
    UnexpectedSyntax,
};
use crate::tests::support::*;
use crate::{
    declaration::derives::derives_clause_normalized,
    lexical::{
        current_item::{CurrentItem, current_item},
        lexer::scan_type_nud_payload,
        position::{advanced_origin, suffix_marker},
        yumark::{FenceOpener, FencePrefixPolicy},
    },
    statement::StatementLineHandoff,
    type_expr::TypeOuterBoundary,
};

#[derive(Clone, Copy)]
enum RecoveryHandling<'a> {
    Reject,
    Discard,
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
    let mut recover = Recover::new_for_test(operators);
    let mut builder = match recovery_handling {
        RecoveryHandling::Frozen(records) | RecoveryHandling::Seeded(Some(records)) => {
            recover = Recover::reconcile_for_test(recover.operators(), records);
            GreenNodeBuilder::new()
        }
        _ => GreenNodeBuilder::new(),
    };
    builder.start_node(SyntaxKind::Root.into());
    if matches!(recovery_handling, RecoveryHandling::Seeded(_)) {
        let seed = derives_record(DerivesRole::ViaTarget, RecoveryKind::Missing, 0..0, 0);
        builder.start_node(SyntaxKind::Missing.into());
        builder.finish_node();
        recover.commit_recovery_for_test(crate::cursor::recovery::RecoveryDraft::new(
            seed.site,
            seed.kind,
            seed.unexpected,
            seed.expectations,
            seed.primary_expectation,
        ));
    }
    let (pending, item_origin, line_entry) = {
        let mut i = crate::cursor::SyntaxIn::new(&mut input, &mut recover, &mut builder);
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
            Some(crate::ambient_claim::AmbientClaimView::root_statement(0)).into(),
        )
    };
    builder.finish_node();
    let (green, recoveries) = match recovery_handling {
        RecoveryHandling::Reject => (finish_without_recoveries(builder, recover), Vec::new()),
        RecoveryHandling::Discard => (
            finish_with_discarded_recoveries(builder, recover),
            Vec::new(),
        ),
        _ => (builder.finish(), recover.finish_recoveries_for_test()),
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
    if kind == SyntaxKind::Error {
        return crate::tests::recovery_output::recovery_groups(&SyntaxNode::new_root(
            green.clone(),
        ))
        .len();
    }
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
                    let role =
                        GrammarRole::Declaration(crate::recovery_record::DeclarationRole::Derives(
                            crate::recovery_record::DerivesRole::RoleReference,
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
fn derives_initial_role_reference_missing_has_direct_ordered_slot() {
    let operators = OperatorTable::empty();
    for (source, leading, payload, remainder, origin, stops) in [
        ("derives", "", None, "", 7, 0),
        ("derives  ", "  ", None, "", 9, 0),
        (
            "derives ]tail",
            " ",
            Some(TokenKind::RBracket),
            "tail",
            9,
            stops_for(TokenKind::RBracket) & crate::lexical::stops::STOP_CLOSES,
        ),
        (
            "derives\nnext",
            "\n",
            Some(TokenKind::Identifier),
            "",
            12,
            0,
        ),
    ] {
        let (green, mut pending, actual_origin, line, actual_remainder, _) = run_derives_with_stops(
            source,
            &operators,
            0,
            LineEntry::InLine,
            None,
            StatementLineHandoff::OrdinaryLayout,
            header_role_boundary(),
            RecoveryHandling::Discard,
            stops,
        );
        assert_eq!(green.to_string(), "derives", "{source:?}");
        assert_eq!(pending.payload_view().token_kind(), payload, "{source:?}");
        assert_eq!(
            pending.payload_view().is_eof(),
            payload.is_none(),
            "{source:?}"
        );
        assert_eq!(
            emit_pending_leading_text(&mut pending),
            leading,
            "{source:?}"
        );
        assert_eq!(pending.payload_view().token_kind(), payload, "{source:?}");
        assert_eq!(actual_origin, origin, "{source:?}");
        assert_eq!(line, LineEntry::InLine, "{source:?}");
        assert_eq!(actual_remainder, remainder, "{source:?}");

        let root = SyntaxNode::new_root(green);
        assert_eq!(root.kind(), SyntaxKind::Root);
        assert_eq!(root.children_with_tokens().count(), 1, "{source:?}");
        let clause = root.children().next().unwrap();
        assert_eq!(clause.kind(), SyntaxKind::DerivesClause);
        assert_eq!(clause.parent(), Some(root.clone()));
        assert_eq!(
            clause.text_range(),
            rowan::TextRange::new(0.into(), 7.into())
        );
        let children = clause.children_with_tokens().collect::<Vec<_>>();
        assert_eq!(children.len(), 2, "{source:?}");
        let keyword = children[0].as_token().unwrap();
        assert_eq!(keyword.kind(), SyntaxKind::DerivesKw);
        assert_eq!(keyword.parent(), Some(clause.clone()));
        assert_eq!(
            keyword.text_range(),
            rowan::TextRange::new(0.into(), 7.into())
        );
        let role = children[1].as_node().unwrap();
        assert_eq!(role.kind(), SyntaxKind::TypeExpression);
        assert_eq!(role.parent(), Some(clause.clone()));
        assert_eq!(role.text_range(), rowan::TextRange::empty(7.into()));
        assert_eq!(role.text().to_string(), "");
        assert_eq!(role.children_with_tokens().count(), 1, "{source:?}");
        let missing = role.children().next().unwrap();
        assert_eq!(missing.kind(), SyntaxKind::Missing);
        assert_eq!(missing.parent(), Some(role.clone()));
        assert_eq!(missing.text_range(), rowan::TextRange::empty(7.into()));
        assert_eq!(missing.children_with_tokens().count(), 0);
        assert_eq!(
            root.descendants_with_tokens()
                .filter(|element| matches!(element.kind(), SyntaxKind::Error | SyntaxKind::Invalid))
                .count(),
            0,
            "{source:?}"
        );
        assert_eq!(
            root.descendants()
                .filter(|node| node.kind() == SyntaxKind::Missing)
                .count(),
            1,
            "{source:?}"
        );
    }
}

#[test]
fn derives_initial_role_reference_error_has_direct_type_primary_slot() {
    let operators = OperatorTable::empty();
    for (source, accepted, retry, leading, payload, remainder, origin, stops) in [
        ("derives @", "derives @", false, "", None, "", 9, 0),
        (
            "derives @ Role",
            "derives @ Role",
            true,
            "",
            None,
            "",
            14,
            0,
        ),
        (
            "derives @ ]tail",
            "derives @",
            false,
            " ",
            Some(TokenKind::RBracket),
            "tail",
            11,
            stops_for(TokenKind::RBracket) & crate::lexical::stops::STOP_CLOSES,
        ),
    ] {
        let (green, mut pending, actual_origin, line, actual_remainder, _) = run_derives_with_stops(
            source,
            &operators,
            0,
            LineEntry::InLine,
            None,
            StatementLineHandoff::OrdinaryLayout,
            header_role_boundary(),
            RecoveryHandling::Discard,
            stops,
        );
        assert_eq!(green.to_string(), accepted, "{source:?}");
        assert_eq!(pending.payload_view().token_kind(), payload, "{source:?}");
        assert_eq!(
            pending.payload_view().is_eof(),
            payload.is_none(),
            "{source:?}"
        );
        assert_eq!(
            emit_pending_leading_text(&mut pending),
            leading,
            "{source:?}"
        );
        assert_eq!(pending.payload_view().token_kind(), payload, "{source:?}");
        assert_eq!(actual_origin, origin, "{source:?}");
        assert_eq!(line, LineEntry::InLine, "{source:?}");
        assert_eq!(actual_remainder, remainder, "{source:?}");

        let root = SyntaxNode::new_root(green);
        let range = rowan::TextRange::new(0.into(), (accepted.len() as u32).into());
        assert_eq!(root.kind(), SyntaxKind::Root);
        assert_eq!(root.text_range(), range);
        assert_eq!(root.children_with_tokens().count(), 1, "{source:?}");
        let clause = root.children().next().unwrap();
        assert_eq!(clause.kind(), SyntaxKind::DerivesClause);
        assert_eq!(clause.parent(), Some(root.clone()));
        assert_eq!(clause.text_range(), range);
        assert_eq!(clause.text().to_string(), accepted);
        let children = clause.children_with_tokens().collect::<Vec<_>>();
        let keyword = children[0].as_token().unwrap();
        assert_eq!(keyword.kind(), SyntaxKind::DerivesKw);
        assert_eq!(keyword.parent(), Some(clause.clone()));
        assert_eq!(
            keyword.text_range(),
            rowan::TextRange::new(0.into(), 7.into())
        );

        let errors = children[1..]
            .iter()
            .take_while(|element| element.kind() == SyntaxKind::Error)
            .collect::<Vec<_>>();
        assert!(!errors.is_empty(), "{source:?}");
        let mut frontier = 7.into();
        for element in &errors {
            let token = element.as_token().unwrap();
            assert_eq!(token.kind(), SyntaxKind::Error);
            assert_eq!(token.parent(), Some(clause.clone()));
            assert_eq!(token.text_range().start(), frontier);
            assert!(!token.text_range().is_empty());
            frontier = token.text_range().end();
        }
        assert_eq!(frontier, 9.into(), "{source:?}");
        assert_eq!(
            children.len(),
            1 + errors.len() + usize::from(retry),
            "{source:?}"
        );
        if retry {
            let role = children.last().unwrap().as_node().unwrap();
            assert_eq!(role.kind(), SyntaxKind::TypeExpression);
            assert_eq!(role.parent(), Some(clause.clone()));
            assert_eq!(
                role.text_range(),
                rowan::TextRange::new(9.into(), 14.into())
            );
            assert_eq!(role.text().to_string(), " Role");
            let whitespace = role.first_child_or_token().unwrap().into_token().unwrap();
            assert_eq!(whitespace.kind(), SyntaxKind::Whitespace);
            assert_eq!(whitespace.parent(), Some(role.clone()));
            assert_eq!(
                whitespace.text_range(),
                rowan::TextRange::new(9.into(), 10.into())
            );
        }
        assert_eq!(
            root.descendants()
                .filter(|node| node.kind() == SyntaxKind::TypeExpression)
                .count(),
            usize::from(retry),
            "{source:?}"
        );
        assert_eq!(
            root.descendants_with_tokens()
                .filter(|element| element.kind() == SyntaxKind::Error)
                .count(),
            errors.len(),
            "{source:?}"
        );
        assert_eq!(
            root.descendants_with_tokens()
                .filter(|element| matches!(
                    element.kind(),
                    SyntaxKind::Missing | SyntaxKind::Invalid | SyntaxKind::ViaKw
                ))
                .count(),
            0,
            "{source:?}"
        );
    }
}

#[test]
fn derives_post_comma_role_reference_missing_has_direct_ordered_slot() {
    let operators = OperatorTable::empty();
    let stops = stops_for(TokenKind::RBracket) & crate::lexical::stops::STOP_CLOSES;
    for (source, leading, payload, remainder, origin) in [
        ("derives Eq,", "", None, "", 11),
        (
            "derives Eq, ]tail",
            " ",
            Some(TokenKind::RBracket),
            "tail",
            13,
        ),
    ] {
        let (green, mut pending, actual_origin, line, actual_remainder, _) = run_derives_with_stops(
            source,
            &operators,
            0,
            LineEntry::InLine,
            None,
            StatementLineHandoff::OrdinaryLayout,
            header_role_boundary(),
            RecoveryHandling::Discard,
            stops,
        );
        assert_eq!(green.to_string(), "derives Eq,", "{source:?}");
        assert_eq!(pending.payload_view().token_kind(), payload, "{source:?}");
        assert_eq!(
            pending.payload_view().is_eof(),
            payload.is_none(),
            "{source:?}"
        );
        assert_eq!(
            emit_pending_leading_text(&mut pending),
            leading,
            "{source:?}"
        );
        assert_eq!(pending.payload_view().token_kind(), payload, "{source:?}");
        assert_eq!(actual_origin, origin, "{source:?}");
        assert_eq!(line, LineEntry::InLine, "{source:?}");
        assert_eq!(actual_remainder, remainder, "{source:?}");

        let root = SyntaxNode::new_root(green);
        let clause_range = rowan::TextRange::new(0.into(), 11.into());
        assert_eq!(root.kind(), SyntaxKind::Root);
        assert_eq!(root.text_range(), clause_range);
        assert_eq!(root.children_with_tokens().count(), 1, "{source:?}");
        let clause = root.children().next().unwrap();
        assert_eq!(clause.kind(), SyntaxKind::DerivesClause);
        assert_eq!(clause.parent(), Some(root.clone()));
        assert_eq!(clause.text_range(), clause_range);
        let children = clause.children_with_tokens().collect::<Vec<_>>();
        assert_eq!(children.len(), 4, "{source:?}");
        let keyword = children[0].as_token().unwrap();
        assert_eq!(keyword.kind(), SyntaxKind::DerivesKw);
        assert_eq!(keyword.parent(), Some(clause.clone()));
        assert_eq!(
            keyword.text_range(),
            rowan::TextRange::new(0.into(), 7.into())
        );
        let accepted = children[1].as_node().unwrap();
        assert_eq!(accepted.kind(), SyntaxKind::TypeExpression);
        assert_eq!(accepted.parent(), Some(clause.clone()));
        assert_eq!(
            accepted.text_range(),
            rowan::TextRange::new(7.into(), 10.into())
        );
        assert_eq!(accepted.text().to_string(), " Eq");
        let comma = children[2].as_token().unwrap();
        assert_eq!(comma.kind(), SyntaxKind::Comma);
        assert_eq!(comma.parent(), Some(clause.clone()));
        assert_eq!(
            comma.text_range(),
            rowan::TextRange::new(10.into(), 11.into())
        );
        let role = children[3].as_node().unwrap();
        assert_eq!(role.kind(), SyntaxKind::TypeExpression);
        assert_eq!(role.parent(), Some(clause.clone()));
        assert_eq!(role.text_range(), rowan::TextRange::empty(11.into()));
        assert_eq!(role.text().to_string(), "");
        assert_eq!(role.children_with_tokens().count(), 1, "{source:?}");
        let missing = role.children().next().unwrap();
        assert_eq!(missing.kind(), SyntaxKind::Missing);
        assert_eq!(missing.parent(), Some(role.clone()));
        assert_eq!(missing.text_range(), rowan::TextRange::empty(11.into()));
        assert_eq!(missing.children_with_tokens().count(), 0);
        assert_eq!(
            root.descendants_with_tokens()
                .filter(|element| matches!(
                    element.kind(),
                    SyntaxKind::Error | SyntaxKind::Invalid | SyntaxKind::ViaKw
                ))
                .count(),
            0,
            "{source:?}"
        );
        assert_eq!(
            root.descendants()
                .filter(|node| node.kind() == SyntaxKind::Missing)
                .count(),
            1,
            "{source:?}"
        );
    }
}

#[test]
fn derives_post_comma_role_reference_error_has_direct_type_primary_slot() {
    let operators = OperatorTable::empty();
    for (source, accepted, retry, leading, payload, remainder, origin, stops) in [
        ("derives Eq, @", "derives Eq, @", false, "", None, "", 13, 0),
        (
            "derives Eq, @ Role",
            "derives Eq, @ Role",
            true,
            "",
            None,
            "",
            18,
            0,
        ),
        (
            "derives Eq, @ ]tail",
            "derives Eq, @",
            false,
            " ",
            Some(TokenKind::RBracket),
            "tail",
            15,
            stops_for(TokenKind::RBracket) & crate::lexical::stops::STOP_CLOSES,
        ),
    ] {
        let (green, mut pending, actual_origin, line, actual_remainder, _) = run_derives_with_stops(
            source,
            &operators,
            0,
            LineEntry::InLine,
            None,
            StatementLineHandoff::OrdinaryLayout,
            header_role_boundary(),
            RecoveryHandling::Discard,
            stops,
        );
        assert_eq!(green.to_string(), accepted, "{source:?}");
        assert_eq!(pending.payload_view().token_kind(), payload, "{source:?}");
        assert_eq!(
            pending.payload_view().is_eof(),
            payload.is_none(),
            "{source:?}"
        );
        assert_eq!(
            emit_pending_leading_text(&mut pending),
            leading,
            "{source:?}"
        );
        assert_eq!(pending.payload_view().token_kind(), payload, "{source:?}");
        assert_eq!(actual_origin, origin, "{source:?}");
        assert_eq!(line, LineEntry::InLine, "{source:?}");
        assert_eq!(actual_remainder, remainder, "{source:?}");

        let root = SyntaxNode::new_root(green);
        let range = rowan::TextRange::new(0.into(), (accepted.len() as u32).into());
        assert_eq!(root.kind(), SyntaxKind::Root);
        assert_eq!(root.text_range(), range);
        assert_eq!(root.children_with_tokens().count(), 1, "{source:?}");
        let clause = root.children().next().unwrap();
        assert_eq!(clause.kind(), SyntaxKind::DerivesClause);
        assert_eq!(clause.parent(), Some(root.clone()));
        assert_eq!(clause.text_range(), range);
        assert_eq!(clause.text().to_string(), accepted);
        let children = clause.children_with_tokens().collect::<Vec<_>>();
        let keyword = children[0].as_token().unwrap();
        assert_eq!(keyword.kind(), SyntaxKind::DerivesKw);
        assert_eq!(keyword.parent(), Some(clause.clone()));
        assert_eq!(
            keyword.text_range(),
            rowan::TextRange::new(0.into(), 7.into())
        );
        let first_role = children[1].as_node().unwrap();
        assert_eq!(first_role.kind(), SyntaxKind::TypeExpression);
        assert_eq!(first_role.parent(), Some(clause.clone()));
        assert_eq!(
            first_role.text_range(),
            rowan::TextRange::new(7.into(), 10.into())
        );
        assert_eq!(first_role.text().to_string(), " Eq");
        let comma = children[2].as_token().unwrap();
        assert_eq!(comma.kind(), SyntaxKind::Comma);
        assert_eq!(comma.parent(), Some(clause.clone()));
        assert_eq!(
            comma.text_range(),
            rowan::TextRange::new(10.into(), 11.into())
        );

        let errors = children[3..]
            .iter()
            .take_while(|element| element.kind() == SyntaxKind::Error)
            .collect::<Vec<_>>();
        assert!(!errors.is_empty(), "{source:?}");
        let mut frontier = 11.into();
        for element in &errors {
            let token = element.as_token().unwrap();
            assert_eq!(token.kind(), SyntaxKind::Error);
            assert_eq!(token.parent(), Some(clause.clone()));
            assert_eq!(token.text_range().start(), frontier);
            assert!(!token.text_range().is_empty());
            frontier = token.text_range().end();
        }
        assert_eq!(frontier, 13.into(), "{source:?}");
        assert_eq!(
            children.len(),
            3 + errors.len() + usize::from(retry),
            "{source:?}"
        );
        if retry {
            let role = children.last().unwrap().as_node().unwrap();
            assert_eq!(role.kind(), SyntaxKind::TypeExpression);
            assert_eq!(role.parent(), Some(clause.clone()));
            assert_eq!(
                role.text_range(),
                rowan::TextRange::new(13.into(), 18.into())
            );
            assert_eq!(role.text().to_string(), " Role");
            let whitespace = role.first_child_or_token().unwrap().into_token().unwrap();
            assert_eq!(whitespace.kind(), SyntaxKind::Whitespace);
            assert_eq!(whitespace.parent(), Some(role.clone()));
            assert_eq!(
                whitespace.text_range(),
                rowan::TextRange::new(13.into(), 14.into())
            );
        }
        assert_eq!(
            root.descendants()
                .filter(|node| node.kind() == SyntaxKind::TypeExpression)
                .count(),
            1 + usize::from(retry),
            "{source:?}"
        );
        assert_eq!(
            root.descendants_with_tokens()
                .filter(|element| element.kind() == SyntaxKind::Error)
                .count(),
            errors.len(),
            "{source:?}"
        );
        assert_eq!(
            root.descendants_with_tokens()
                .filter(|element| matches!(
                    element.kind(),
                    SyntaxKind::Missing | SyntaxKind::Invalid | SyntaxKind::ViaKw
                ))
                .count(),
            0,
            "{source:?}"
        );
    }
}

#[test]
fn derives_role_episode_repetition_has_one_compositional_rowan_schema() {
    use SyntaxKind::{Comma, DerivesKw, Error, Identifier, TypeExpression, ViaKw, Whitespace};

    struct Row {
        source: &'static str,
        committed: usize,
        children: Vec<(SyntaxKind, bool, std::ops::Range<usize>)>,
        episodes: usize,
        missing_ordinals: Vec<usize>,
        error_ordinals: Vec<usize>,
        pending: Option<TokenKind>,
        leading: &'static str,
        origin: usize,
        remainder: &'static str,
    }

    let operators = OperatorTable::empty();
    for row in [
        Row {
            source: "derives,,",
            committed: 9,
            children: vec![
                (DerivesKw, false, 0..7),
                (TypeExpression, true, 7..7),
                (Comma, false, 7..8),
                (TypeExpression, true, 8..8),
                (Comma, false, 8..9),
                (TypeExpression, true, 9..9),
            ],
            episodes: 3,
            missing_ordinals: vec![0, 1, 2],
            error_ordinals: vec![],
            pending: None,
            leading: "",
            origin: 9,
            remainder: "",
        },
        Row {
            source: "derives @, Debug,",
            committed: 17,
            children: vec![
                (DerivesKw, false, 0..7),
                (Error, false, 7..8),
                (Error, false, 8..9),
                (Comma, false, 9..10),
                (TypeExpression, true, 10..16),
                (Comma, false, 16..17),
                (TypeExpression, true, 17..17),
            ],
            episodes: 3,
            missing_ordinals: vec![2],
            error_ordinals: vec![0],
            pending: None,
            leading: "",
            origin: 17,
            remainder: "",
        },
        Row {
            source: "derives @ Eq ,",
            committed: 14,
            children: vec![
                (DerivesKw, false, 0..7),
                (Error, false, 7..8),
                (Error, false, 8..9),
                (TypeExpression, true, 9..12),
                (Whitespace, false, 12..13),
                (Comma, false, 13..14),
                (TypeExpression, true, 14..14),
            ],
            episodes: 2,
            missing_ordinals: vec![1],
            error_ordinals: vec![0],
            pending: None,
            leading: "",
            origin: 14,
            remainder: "",
        },
        Row {
            source: "derives via target,tail",
            committed: 18,
            children: vec![
                (DerivesKw, false, 0..7),
                (TypeExpression, true, 7..7),
                (Whitespace, false, 7..8),
                (ViaKw, false, 8..11),
                (Whitespace, false, 11..12),
                (Identifier, false, 12..18),
            ],
            episodes: 1,
            missing_ordinals: vec![0],
            error_ordinals: vec![],
            pending: Some(TokenKind::Comma),
            leading: "",
            origin: 19,
            remainder: "tail",
        },
        Row {
            source: "derives @ via target",
            committed: 20,
            children: vec![
                (DerivesKw, false, 0..7),
                (Error, false, 7..8),
                (Error, false, 8..9),
                (Whitespace, false, 9..10),
                (ViaKw, false, 10..13),
                (Whitespace, false, 13..14),
                (Identifier, false, 14..20),
            ],
            episodes: 1,
            missing_ordinals: vec![],
            error_ordinals: vec![0],
            pending: None,
            leading: "",
            origin: 20,
            remainder: "",
        },
        Row {
            source: "derives Eq, @ Role via target,tail",
            committed: 29,
            children: vec![
                (DerivesKw, false, 0..7),
                (TypeExpression, true, 7..10),
                (Comma, false, 10..11),
                (Error, false, 11..12),
                (Error, false, 12..13),
                (TypeExpression, true, 13..18),
                (Whitespace, false, 18..19),
                (ViaKw, false, 19..22),
                (Whitespace, false, 22..23),
                (Identifier, false, 23..29),
            ],
            episodes: 2,
            missing_ordinals: vec![],
            error_ordinals: vec![1],
            pending: Some(TokenKind::Comma),
            leading: "",
            origin: 30,
            remainder: "tail",
        },
        Row {
            source: "derives Eq, Debug, ]tail",
            committed: 18,
            children: vec![
                (DerivesKw, false, 0..7),
                (TypeExpression, true, 7..10),
                (Comma, false, 10..11),
                (TypeExpression, true, 11..17),
                (Comma, false, 17..18),
                (TypeExpression, true, 18..18),
            ],
            episodes: 3,
            missing_ordinals: vec![2],
            error_ordinals: vec![],
            pending: Some(TokenKind::RBracket),
            leading: " ",
            origin: 20,
            remainder: "tail",
        },
    ] {
        let stops = if row.pending == Some(TokenKind::RBracket) {
            stops_for(TokenKind::RBracket) & crate::lexical::stops::STOP_CLOSES
        } else {
            0
        };
        let (green, mut pending, origin, line, remainder, _) = run_derives_with_stops(
            row.source,
            &operators,
            0,
            LineEntry::InLine,
            None,
            StatementLineHandoff::OrdinaryLayout,
            header_role_boundary(),
            RecoveryHandling::Discard,
            stops,
        );
        assert_eq!(green.to_string(), &row.source[..row.committed]);
        assert_eq!(pending.payload_view().token_kind(), row.pending);
        assert_eq!(pending.payload_view().is_eof(), row.pending.is_none());
        assert_eq!(emit_pending_leading_text(&mut pending), row.leading);
        assert_eq!(pending.payload_view().token_kind(), row.pending);
        assert_eq!(origin, row.origin, "{:?}", row.source);
        assert_eq!(line, LineEntry::InLine);
        assert_eq!(remainder, row.remainder);

        let root = SyntaxNode::new_root(green);
        assert_eq!(root.kind(), SyntaxKind::Root);
        assert_eq!(root.children_with_tokens().count(), 1);
        let clause = root.children().next().unwrap();
        assert_eq!(clause.kind(), SyntaxKind::DerivesClause);
        assert_eq!(clause.parent(), Some(root.clone()));
        let range = rowan::TextRange::new(0.into(), (row.committed as u32).into());
        assert_eq!(root.text_range(), range);
        assert_eq!(clause.text_range(), range);
        let children = clause.children_with_tokens().collect::<Vec<_>>();
        assert_eq!(
            children
                .iter()
                .map(|element| (
                    element.kind(),
                    element.as_node().is_some(),
                    usize::from(element.text_range().start())
                        ..usize::from(element.text_range().end()),
                ))
                .collect::<Vec<_>>(),
            row.children,
            "{:?}",
            row.source
        );

        // Episode ordinals follow committed commas, including slots without a Type node.
        let mut ordinal = 0;
        let mut via = false;
        let mut missing_ordinals = Vec::new();
        let mut error_ordinals = Vec::new();
        for (index, element) in children.iter().enumerate() {
            assert_eq!(element.parent(), Some(clause.clone()));
            match element.kind() {
                Comma => {
                    assert!(!via);
                    ordinal += 1;
                }
                ViaKw => {
                    assert!(!via);
                    via = true;
                }
                Error => {
                    assert!(!via);
                    assert!(!element.text_range().is_empty());
                    if children[index - 1].kind() == Error {
                        assert_eq!(
                            children[index - 1].text_range().end(),
                            element.text_range().start()
                        );
                    } else {
                        error_ordinals.push(ordinal);
                    }
                }
                TypeExpression => {
                    assert!(!via);
                    let role = element.as_node().unwrap();
                    if role.text_range().is_empty() {
                        assert!(!error_ordinals.contains(&ordinal));
                        missing_ordinals.push(ordinal);
                        assert_eq!(role.children_with_tokens().count(), 1);
                        let missing = role.children().next().unwrap();
                        assert_eq!(missing.kind(), SyntaxKind::Missing);
                        assert_eq!(missing.parent(), Some(role.clone()));
                        assert_eq!(missing.text_range(), role.text_range());
                        assert_eq!(missing.children_with_tokens().count(), 0);
                    } else {
                        let leading = role.first_child_or_token().unwrap();
                        assert_eq!(leading.kind(), Whitespace);
                        assert!(leading.as_token().is_some());
                        assert_eq!(leading.parent(), Some(role.clone()));
                        assert_eq!(leading.text_range().start(), role.text_range().start());
                        assert_eq!(leading.text_range().len(), 1.into());
                    }
                }
                _ => {}
            }
        }
        assert_eq!(ordinal + 1, row.episodes);
        assert_eq!(missing_ordinals, row.missing_ordinals);
        assert_eq!(error_ordinals, row.error_ordinals);
        assert_eq!(
            root.descendants()
                .filter(|node| node.kind() == SyntaxKind::Missing)
                .count(),
            missing_ordinals.len()
        );
        assert_eq!(
            root.descendants_with_tokens()
                .filter(|element| element.kind() == Error)
                .count(),
            children
                .iter()
                .filter(|element| element.kind() == Error)
                .count()
        );
        assert!(root.descendants().all(|node| matches!(
            node.kind(),
            SyntaxKind::Root | SyntaxKind::DerivesClause | TypeExpression | SyntaxKind::Missing
        )));
    }
}

#[test]
fn derives_via_target_raw_slot_has_direct_missing_and_error_retry() {
    struct Row {
        source: &'static str,
        tree: &'static str,
        pending_leading: &'static str,
        direct_children: Vec<(SyntaxKind, std::ops::Range<usize>)>,
        missing: Option<std::ops::Range<usize>>,
        errors: Vec<std::ops::Range<usize>>,
        retry: Option<std::ops::Range<usize>>,
    }

    let operators = OperatorTable::empty();
    for row in [
        Row {
            source: "derives Eq via",
            tree: "derives Eq via",
            pending_leading: "",
            direct_children: vec![
                (SyntaxKind::DerivesKw, 0..7),
                (SyntaxKind::TypeExpression, 7..10),
                (SyntaxKind::Whitespace, 10..11),
                (SyntaxKind::ViaKw, 11..14),
                (SyntaxKind::Missing, 14..14),
            ],
            missing: Some(14..14),
            errors: vec![],
            retry: None,
        },
        Row {
            source: "derives Eq via  ",
            tree: "derives Eq via",
            pending_leading: "  ",
            direct_children: vec![
                (SyntaxKind::DerivesKw, 0..7),
                (SyntaxKind::TypeExpression, 7..10),
                (SyntaxKind::Whitespace, 10..11),
                (SyntaxKind::ViaKw, 11..14),
                (SyntaxKind::Missing, 14..14),
            ],
            missing: Some(14..14),
            errors: vec![],
            retry: None,
        },
        Row {
            source: "derives Eq via @ target",
            tree: "derives Eq via @ target",
            pending_leading: "",
            direct_children: vec![
                (SyntaxKind::DerivesKw, 0..7),
                (SyntaxKind::TypeExpression, 7..10),
                (SyntaxKind::Whitespace, 10..11),
                (SyntaxKind::ViaKw, 11..14),
                (SyntaxKind::Error, 14..15),
                (SyntaxKind::Error, 15..16),
                (SyntaxKind::Whitespace, 16..17),
                (SyntaxKind::Identifier, 17..23),
            ],
            missing: None,
            errors: vec![14..15, 15..16],
            retry: Some(17..23),
        },
    ] {
        let (green, pending, origin, line, remainder, _) = run_derives_normalized(
            row.source,
            &operators,
            0,
            LineEntry::InLine,
            None,
            StatementLineHandoff::OrdinaryLayout,
            header_role_boundary(),
            RecoveryHandling::Discard,
        );
        assert_eq!(green.to_string(), row.tree, "{:?}", row.source);
        let mut pending = pending;
        assert!(pending.payload_view().is_eof(), "{:?}", row.source);
        assert_eq!(emit_pending_leading_text(&mut pending), row.pending_leading);
        assert!(pending.payload_view().is_eof(), "{:?}", row.source);
        assert_eq!(origin, row.source.len(), "{:?}", row.source);
        assert_eq!(line, LineEntry::InLine, "{:?}", row.source);
        assert_eq!(remainder, "", "{:?}", row.source);

        let root = SyntaxNode::new_root(green);
        let clause = root.children().next().unwrap();
        assert_eq!(clause.kind(), SyntaxKind::DerivesClause, "{:?}", row.source);
        assert_eq!(
            clause
                .children_with_tokens()
                .map(|element| {
                    (
                        element.kind(),
                        usize::from(element.text_range().start())
                            ..usize::from(element.text_range().end()),
                    )
                })
                .collect::<Vec<_>>(),
            row.direct_children,
            "{:?}",
            row.source
        );
        assert!(
            root.descendants()
                .all(|node| node.kind() != SyntaxKind::Invalid),
            "{:?}: {root:#?}",
            row.source
        );

        let missing = clause
            .children()
            .filter(|node| node.kind() == SyntaxKind::Missing)
            .collect::<Vec<_>>();
        let errors = clause
            .children_with_tokens()
            .filter_map(|element| element.into_token())
            .filter(|token| token.kind() == SyntaxKind::Error)
            .collect::<Vec<_>>();
        if let Some(range) = row.missing {
            assert_eq!(missing.len(), 1);
            assert_eq!(missing[0].parent(), Some(clause.clone()));
            assert_eq!(
                missing[0].text_range(),
                rowan::TextRange::new((range.start as u32).into(), (range.end as u32).into())
            );
            assert!(errors.is_empty());
        } else {
            assert!(missing.is_empty());
            assert!(
                errors
                    .iter()
                    .all(|token| token.parent() == Some(clause.clone()))
            );
            assert_eq!(
                errors
                    .iter()
                    .map(|token| token.text_range())
                    .collect::<Vec<_>>(),
                row.errors
                    .iter()
                    .map(|range| {
                        rowan::TextRange::new(
                            (range.start as u32).into(),
                            (range.end as u32).into(),
                        )
                    })
                    .collect::<Vec<_>>()
            );
            let range = row.retry.unwrap();
            let retry = clause
                .children_with_tokens()
                .find(|element| {
                    element.kind() == SyntaxKind::Identifier
                        && element.text_range()
                            == rowan::TextRange::new(
                                (range.start as u32).into(),
                                (range.end as u32).into(),
                            )
                })
                .unwrap();
            assert_eq!(retry.parent(), Some(clause.clone()));
        }
    }
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
                let error =
                    crate::tests::recovery_output::recovery_groups(&SyntaxNode::new_root(green))
                        .into_iter()
                        .next()
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
    use crate::lexical::stops::{STOP_ELSE, STOP_ELSIF};
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
