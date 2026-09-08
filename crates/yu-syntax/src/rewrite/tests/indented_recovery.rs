use super::*;
use crate::{rewrite::ambient_claim::AmbientClaimView, session::*};
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
    let mut recover = Recover::new(&operators);
    let mut output = frozen
        .map(GreenNodeBuilder::reconcile)
        .unwrap_or_else(GreenNodeBuilder::new);
    output.start_node(SyntaxKind::Root.into());
    let exit = statement_normalized(
        In::new(&mut input, &mut recover, &mut output),
        0,
        stops,
        origin,
        LineEntry::InLine,
        fence,
        Some(AmbientClaimView::root_statement(0)).into(),
        Some(crate::rewrite::sequence::SequenceOwner::RootStatement),
    );
    output.finish_node();
    let (green, records) = output.finish_with_recoveries();
    (green, records, exit, input)
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
    use crate::rewrite::operator::STOP_COMMA;
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
fn indented_quoted_fence_and_utf8_crlf_use_physical_shifted_extents() {
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
            let mut recover = Recover::new(&operators);
            let mut output = frozen_records
                .as_deref()
                .map(GreenNodeBuilder::reconcile)
                .unwrap_or_else(GreenNodeBuilder::new);
            output.start_node(SyntaxKind::Root.into());
            let exit = crate::rewrite::statement::indented_statement_block_normalized(
                In::new(&mut input, &mut recover, &mut output),
                0,
                role,
                STOP_ELSE,
                100,
                LineEntry::InLine,
                Some(&fence),
                Some(AmbientClaimView::root_statement(0)).into(),
            );
            output.finish_node();
            let (green, records) = output.finish_with_recoveries();
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
