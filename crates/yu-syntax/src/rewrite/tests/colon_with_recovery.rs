use super::*;
use crate::{
    rewrite::{ambient_claim::AmbientClaimView, driver::MlMode, statement::StatementLineHandoff},
    session::{
        ColonApplicationRole, DiagnosticId, ExpectationSources, ExpectedSyntax, GrammarRole,
        PunctuationEvidence, RecoveryKind, RecoverySiteKey, SyntaxExpectation, UnexpectedCategory,
        UnexpectedSyntax, WithBodyRole,
    },
};
use std::{ops::Range, sync::Arc};

fn record(
    role: GrammarRole,
    expected: ExpectedSyntax,
    kind: RecoveryKind,
    range: Range<usize>,
) -> CommittedRecoveryRecord {
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
            expected,
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
    let mut recover = Recover::new(&operators);
    let mut output = frozen
        .map(GreenNodeBuilder::reconcile)
        .unwrap_or_else(GreenNodeBuilder::new);
    output.start_node(SyntaxKind::Root.into());
    let exit = expr_normalized(
        In::new(&mut input, &mut recover, &mut output),
        None,
        0,
        stops,
        MlMode::All,
        StatementLineHandoff::OrdinaryLayout,
        origin,
        LineEntry::InLine,
        fence,
        Some(AmbientClaimView::root_statement(0)).into(),
        None,
    )
    .unwrap();
    output.finish_node();
    let (green, records) = output.finish_with_recoveries();
    (green, records, exit, input)
}

#[test]
fn inline_slots_have_exact_fresh_and_frozen_records() {
    use RecoveryKind::{Error, Missing};
    let rhs = GrammarRole::ColonApplication(ColonApplicationRole::Rhs);
    let arg = GrammarRole::ColonApplication(ColonApplicationRole::InlineArgument);
    let intro = GrammarRole::WithBody(WithBodyRole::Introducer);
    let body = GrammarRole::WithBody(WithBodyRole::Body);
    for (source, role, expected, kind, range) in [
        ("f:", rhs, ExpectedSyntax::Expression, Missing, 2..2),
        ("f:   ", rhs, ExpectedSyntax::Expression, Missing, 5..5),
        ("f: , x", rhs, ExpectedSyntax::Expression, Missing, 2..2),
        ("f: x,", arg, ExpectedSyntax::Expression, Missing, 5..5),
        ("f: @ @ x", rhs, ExpectedSyntax::Expression, Error, 3..6),
        ("f: => x", rhs, ExpectedSyntax::Expression, Error, 3..5),
        ("f: @ ]", rhs, ExpectedSyntax::Expression, Error, 3..4),
        (
            "f with",
            intro,
            ExpectedSyntax::Punctuation(PunctuationEvidence::Colon),
            Missing,
            6..6,
        ),
        (
            "f with x",
            intro,
            ExpectedSyntax::Punctuation(PunctuationEvidence::Colon),
            Missing,
            6..6,
        ),
        (
            "f with :: x",
            intro,
            ExpectedSyntax::Punctuation(PunctuationEvidence::Colon),
            Missing,
            6..6,
        ),
        ("f with: ", body, ExpectedSyntax::Statement, Missing, 8..8),
        (
            "f with:\nnext",
            body,
            ExpectedSyntax::Statement,
            Missing,
            7..7,
        ),
        ("f with: ;", body, ExpectedSyntax::Statement, Missing, 7..7),
        (
            "f with ;",
            intro,
            ExpectedSyntax::Punctuation(PunctuationEvidence::Colon),
            Missing,
            6..6,
        ),
        (
            "f with: @ @ x",
            body,
            ExpectedSyntax::Statement,
            Error,
            8..11,
        ),
    ] {
        let (green, records, _, _) = parse(source, 0, 0, None, None);
        assert_eq!(records, [record(role, expected, kind, range)], "{source:?}");
        if kind == RecoveryKind::Error {
            let error = SyntaxNode::new_root(green.clone())
                .descendants()
                .find(|node| node.kind() == SyntaxKind::Error)
                .expect("typed Error product");
            assert_eq!(
                error.text().to_string(),
                source[records[0].site.range.clone()]
            );
        }
        let (again, frozen, _, _) = parse(source, 0, 0, None, Some(&records));
        assert_eq!(again, green);
        assert_eq!(frozen, records);
    }
}

#[test]
fn with_retry_admits_canonical_statements_and_literals() {
    for body in [
        "x",
        "pub x = y",
        "use x",
        "struct X {}",
        "pub enum E;",
        "pub error E;",
        "pub role R;",
        "pub impl T;",
        "pub cast(x): T;",
        "pub act A;",
        "\"text\"",
        "\"\"\"raw\"\"\"",
        "~\"raw\"",
    ] {
        for prefix in ["f with: ", "f with: @ @ "] {
            let source = format!("{prefix}{body}");
            let (green, records, _, _) = parse(&source, 0, 0, None, None);
            assert_eq!(green.to_string(), source);
            let expected = if prefix.contains('@') {
                vec![record(
                    GrammarRole::WithBody(WithBodyRole::Body),
                    ExpectedSyntax::Statement,
                    RecoveryKind::Error,
                    8..11,
                )]
            } else {
                vec![]
            };
            assert_eq!(records, expected, "{source:?}");
            let (again, frozen, _, _) = parse(&source, 0, 0, None, Some(&records));
            assert_eq!(again, green);
            assert_eq!(frozen, records);
        }
    }
}

#[test]
fn inline_boundaries_preserve_the_whole_pending_item() {
    use crate::rewrite::operator::STOP_COMMA;
    for (source, stops, emitted, pending, start, role, kind, range) in [
        (
            "f: , x",
            STOP_COMMA,
            "f:",
            TokenKind::Comma,
            2,
            GrammarRole::ColonApplication(ColonApplicationRole::Rhs),
            RecoveryKind::Missing,
            2..2,
        ),
        (
            "f: @ ]",
            0,
            "f: @",
            TokenKind::RBracket,
            4,
            GrammarRole::ColonApplication(ColonApplicationRole::Rhs),
            RecoveryKind::Error,
            3..4,
        ),
        (
            "f: @ , x",
            STOP_COMMA,
            "f: @",
            TokenKind::Comma,
            4,
            GrammarRole::ColonApplication(ColonApplicationRole::Rhs),
            RecoveryKind::Error,
            3..4,
        ),
        (
            "f: -> x",
            STOP_ARROW,
            "f:",
            TokenKind::Arrow,
            2,
            GrammarRole::ColonApplication(ColonApplicationRole::Rhs),
            RecoveryKind::Missing,
            2..2,
        ),
        (
            "f with: @ ]",
            0,
            "f with: @",
            TokenKind::RBracket,
            9,
            GrammarRole::WithBody(WithBodyRole::Body),
            RecoveryKind::Error,
            8..9,
        ),
        (
            "f with :: x",
            0,
            "f with",
            TokenKind::PathSeparator,
            6,
            GrammarRole::WithBody(WithBodyRole::Introducer),
            RecoveryKind::Missing,
            6..6,
        ),
    ] {
        let (green, records, exit, remainder) = parse(source, stops, 0, None, None);
        let expected = match role {
            GrammarRole::ColonApplication(_) => ExpectedSyntax::Expression,
            GrammarRole::WithBody(WithBodyRole::Introducer) => {
                ExpectedSyntax::Punctuation(PunctuationEvidence::Colon)
            }
            _ => ExpectedSyntax::Statement,
        };
        assert_eq!(records, [record(role, expected, kind, range)], "{source:?}");
        assert_eq!(green.to_string(), emitted);
        let NormalizedExit::Complete(Err(Either::Left(item)), _) = exit else {
            panic!("pending boundary")
        };
        assert_eq!(token_kind(&item), Some(pending));
        assert_eq!(
            item.extent(source.len() - remainder.len())
                .recovery_range()
                .start,
            start
        );
        let (again, frozen, _, _) = parse(source, stops, 0, None, Some(&records));
        assert_eq!(again, green);
        assert_eq!(frozen, records);
    }
}

#[test]
fn inline_utf8_crlf_and_quoted_fences_keep_physical_coordinates() {
    use crate::rewrite::yumark::{FenceOpener, FencePrefixPolicy};
    let fence = FenceBoundary {
        opener: FenceOpener {
            line: 0,
            marker: 0..3,
            marker_width: 3,
        },
        prefix_policy: FencePrefixPolicy::ActivePrefixQuote { depth: 2, base: 0 },
        close_column: 0,
    };
    for (source, role, expected, kind, range, emitted) in [
        (
            "f:\r\n> > ```\nouter",
            GrammarRole::ColonApplication(ColonApplicationRole::Rhs),
            ExpectedSyntax::Expression,
            RecoveryKind::Missing,
            104..104,
            "f:",
        ),
        (
            "f: 💥\r\n> > ```\nouter",
            GrammarRole::ColonApplication(ColonApplicationRole::Rhs),
            ExpectedSyntax::Expression,
            RecoveryKind::Error,
            103..107,
            "f: 💥",
        ),
        (
            "f with:\r\n> > ```\nouter",
            GrammarRole::WithBody(WithBodyRole::Body),
            ExpectedSyntax::Statement,
            RecoveryKind::Missing,
            109..109,
            "f with:",
        ),
        (
            "f with: 💥\r\n> > ```\nouter",
            GrammarRole::WithBody(WithBodyRole::Body),
            ExpectedSyntax::Statement,
            RecoveryKind::Error,
            108..112,
            "f with: 💥",
        ),
    ] {
        let (green, records, exit, remainder) = parse(source, 0, 100, Some(&fence), None);
        assert_eq!(records, [record(role, expected, kind, range)]);
        assert_eq!(green.to_string(), emitted);
        assert_eq!(remainder, "> > ```\nouter");
        assert!(matches!(
            exit,
            NormalizedExit::Complete(Err(Either::Left(_)), LineEntry::PhysicalStart)
        ));
        let (again, frozen, _, _) = parse(source, 0, 100, Some(&fence), Some(&records));
        assert_eq!(again, green);
        assert_eq!(frozen, records);
    }
    let source = "f with @\r\n> > ```\nouter";
    let (green, records, exit, remainder) = parse(source, 0, 100, Some(&fence), None);
    let intro = record(
        GrammarRole::WithBody(WithBodyRole::Introducer),
        ExpectedSyntax::Punctuation(PunctuationEvidence::Colon),
        RecoveryKind::Missing,
        106..106,
    );
    let mut body = record(
        GrammarRole::WithBody(WithBodyRole::Body),
        ExpectedSyntax::Statement,
        RecoveryKind::Error,
        107..108,
    );
    body.id = DiagnosticId(1);
    assert_eq!(records, [intro, body]);
    assert_eq!(green.to_string(), "f with @");
    assert_eq!(remainder, "> > ```\nouter");
    assert!(matches!(
        exit,
        NormalizedExit::Complete(Err(Either::Left(_)), LineEntry::PhysicalStart)
    ));
    let (again, frozen, _, _) = parse(source, 0, 100, Some(&fence), Some(&records));
    assert_eq!(again, green);
    assert_eq!(frozen, records);
}

#[test]
fn inline_nested_slots_keep_distinct_roles_and_frozen_ids() {
    let source = "f with x:";
    let (green, records, _, _) = parse(source, 0, 0, None, None);
    let first = record(
        GrammarRole::WithBody(WithBodyRole::Introducer),
        ExpectedSyntax::Punctuation(PunctuationEvidence::Colon),
        RecoveryKind::Missing,
        6..6,
    );
    let mut second = record(
        GrammarRole::ColonApplication(ColonApplicationRole::Rhs),
        ExpectedSyntax::Expression,
        RecoveryKind::Missing,
        9..9,
    );
    second.id = DiagnosticId(1);
    assert_eq!(records, [first, second]);
    let (again, frozen, _, _) = parse(source, 0, 0, None, Some(&records));
    assert_eq!(again, green);
    assert_eq!(frozen, records);
}

#[test]
fn with_false_prefixed_declaration_candidate_keeps_canonical_fallback() {
    let source = "f with: @ my use";
    let (green, records, _, _) = parse(source, 0, 0, None, None);
    assert_eq!(green.to_string(), source);
    assert_eq!(
        records,
        [record(
            GrammarRole::WithBody(WithBodyRole::Body),
            ExpectedSyntax::Statement,
            RecoveryKind::Error,
            8..9
        )]
    );
    let root = SyntaxNode::new_root(green);
    assert!(
        !root
            .descendants()
            .any(|node| node.kind() == SyntaxKind::UseDeclaration)
    );
}

#[test]
fn colon_disabled_ml_entry_keeps_seed_and_pending_colon_effect_free() {
    let operators = OperatorTable::empty();
    let mut recover = Recover::new(&operators);
    let mut input = "f: @";
    let mut output = GreenNodeBuilder::new();
    output.start_node(SyntaxKind::Root.into());
    output.token(SyntaxKind::Identifier.into(), "seed");
    let exit = expr_normalized(
        In::new(&mut input, &mut recover, &mut output),
        None,
        0,
        0,
        MlMode::None,
        StatementLineHandoff::OrdinaryLayout,
        100,
        LineEntry::InLine,
        None,
        Some(AmbientClaimView::root_statement(0)).into(),
        None,
    )
    .unwrap();
    output.finish_node();
    let (green, records) = output.finish_with_recoveries();
    assert_eq!(green.to_string(), "seedf");
    assert!(records.is_empty());
    assert_eq!(input, " @");
    let NormalizedExit::Complete(Err(Either::Left(item)), _) = exit else {
        panic!("unread colon")
    };
    assert_eq!(token_kind(&item), Some(TokenKind::Colon));
    assert_eq!(item.extent(102).recovery_range(), 101..102);
}

#[test]
fn inline_recovery_allocates_after_seeded_and_frozen_records() {
    use crate::rewrite::output::RecoveryDraft;
    let role = GrammarRole::WithBody(WithBodyRole::Body);
    let mut seed = record(role, ExpectedSyntax::Statement, RecoveryKind::Missing, 0..0);
    seed.id = DiagnosticId(7);
    let mut reused = record(role, ExpectedSyntax::Statement, RecoveryKind::Error, 18..19);
    reused.id = DiagnosticId(19);
    let frozen = [seed.clone(), reused.clone()];
    for reconcile in [false, true] {
        let operators = OperatorTable::empty();
        let mut recover = Recover::new(&operators);
        let mut output = if reconcile {
            GreenNodeBuilder::reconcile(&frozen)
        } else {
            GreenNodeBuilder::new()
        };
        output.start_node(SyntaxKind::Root.into());
        output.token(SyntaxKind::Identifier.into(), "seed");
        output.start_node(SyntaxKind::Missing.into());
        output.finish_node();
        output.commit_recovery(RecoveryDraft::new(
            seed.site.clone(),
            seed.kind,
            seed.unexpected.clone(),
            seed.expectations.clone(),
            0,
        ));
        for origin in [10, 20] {
            let mut input = "f with: @";
            expr_normalized(
                In::new(&mut input, &mut recover, &mut output),
                None,
                0,
                0,
                MlMode::All,
                StatementLineHandoff::OrdinaryLayout,
                origin,
                LineEntry::InLine,
                None,
                Some(AmbientClaimView::root_statement(0)).into(),
                None,
            )
            .unwrap();
            assert_eq!(input, "");
        }
        output.finish_node();
        let (green, records) = output.finish_with_recoveries();
        assert_eq!(green.to_string(), "seedf with: @f with: @");
        let mut expected_seed = seed.clone();
        expected_seed.id = DiagnosticId(if reconcile { 7 } else { 0 });
        let mut expected_reused = reused.clone();
        expected_reused.id = DiagnosticId(if reconcile { 19 } else { 1 });
        let mut last = record(role, ExpectedSyntax::Statement, RecoveryKind::Error, 28..29);
        last.id = DiagnosticId(if reconcile { 20 } else { 2 });
        assert_eq!(records, [expected_seed, expected_reused, last]);
    }
}

#[test]
fn line_deferred_with_preserves_the_whole_keyword_without_records() {
    let (green, records, exit, remainder) = parse("f\nwith x", 0, 0, None, None);
    assert_eq!(green.to_string(), "f");
    assert!(records.is_empty());
    assert_eq!(remainder, " x");
    let NormalizedExit::Complete(Err(Either::Left(item)), _) = exit else {
        panic!("pending keyword")
    };
    assert_eq!(item.payload_view().spelling(), Some("with"));
    assert_eq!(item.extent(6).recovery_range(), 1..6);
}
