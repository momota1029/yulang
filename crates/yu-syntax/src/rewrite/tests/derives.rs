use reborrow_generic::Reborrow as _;
use std::sync::Arc;

use super::*;
use crate::rewrite::{
    current_item::{CurrentItem, current_item},
    derives::derives_clause_normalized,
    driver::{advanced_origin, suffix_marker},
    lexer::scan_type_nud_payload,
    statement::StatementLineHandoff,
    type_expr::TypeOuterBoundary,
    yumark::{FenceOpener, FencePrefixPolicy},
};
use crate::session::{
    DiagnosticId, ExpectationSources, ExpectedSyntax, GrammarRole, RecoveryKind, RecoverySiteKey,
    SyntaxExpectation, TypeRole, UnexpectedCategory, UnexpectedSyntax,
};

#[derive(Clone, Copy)]
enum RecoveryHandling {
    Reject,
    Retain,
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
    recovery_handling: RecoveryHandling,
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
    let mut builder = GreenNodeBuilder::new();
    builder.start_node(SyntaxKind::Root.into());
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
            0,
            line_handoff,
            role_boundary,
            item_origin,
            next_line_entry,
            fence,
            Some(crate::rewrite::ambient_claim::AmbientClaimView::root_statement(0)).into(),
        )
    };
    builder.finish_node();
    let (green, recoveries) = match recovery_handling {
        RecoveryHandling::Reject => (builder.finish(), Vec::new()),
        RecoveryHandling::Retain => builder.finish_with_recoveries(),
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
        ("> > derives", 1, 0, Vec::new()),
        (
            "> > derives Eq, via",
            2,
            0,
            vec![{
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
            }],
        ),
        (
            "> > derives @ Role via @ target",
            0,
            2,
            vec![required_type_primary_error_record()],
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
            RecoveryHandling::Reject,
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
