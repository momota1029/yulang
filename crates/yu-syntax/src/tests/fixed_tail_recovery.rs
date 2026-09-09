use crate::tests::support::*;
use crate::{
    ambient_claim::AmbientClaimView,
    handoff::MlMode,
    recovery_record::{
        DiagnosticId, ExpectationSources, ExpectedSyntax, ExpressionRole, GrammarRole,
        RecoveryKind, RecoverySiteKey, SyntaxExpectation, UnexpectedCategory, UnexpectedSyntax,
    },
    statement::StatementLineHandoff,
};
use std::{ops::Range, sync::Arc};

fn record(
    role: ExpressionRole,
    kind: RecoveryKind,
    range: Range<usize>,
) -> CommittedRecoveryRecord {
    let role = GrammarRole::Expression(role);
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
            expected: ExpectedSyntax::Identifier,
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
    let exit = expr_normalized(
        crate::cursor::SyntaxIn::new(&mut input, &mut recover, &mut output),
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
    let (green, records) = (output.finish(), recover.finish_recoveries_for_test());
    (green, records, exit, input)
}

#[test]
fn fixed_tail_slots_publish_exact_fresh_and_frozen_records() {
    use ExpressionRole::{FieldName, PathSegment};
    use RecoveryKind::{Error, Missing};
    for (source, role, kind, range) in [
        ("x.", FieldName, Missing, 2..2),
        ("x.@", FieldName, Error, 2..3),
        ("x::", PathSegment, Missing, 3..3),
        ("x::  ", PathSegment, Missing, 5..5),
        ("x::123", PathSegment, Error, 3..6),
        ("x. field", FieldName, Missing, 2..2),
        ("x:: 123", PathSegment, Error, 4..7),
        ("x::::name", PathSegment, Missing, 3..3),
        ("x::::$name", PathSegment, Missing, 3..3),
    ] {
        let (green, actual, _, _) = parse(source, 0, 0, None, None);
        assert_eq!(actual, [record(role, kind, range)], "{source:?}");
        assert_eq!(green.to_string(), source);
        let (again, frozen, _, _) = parse(source, 0, 0, None, Some(&actual));
        assert_eq!(again, green);
        assert_eq!(frozen, actual);
    }
}

#[test]
fn path_error_keeps_each_adjacent_sigil_retry_item() {
    for name in ["$name", "&name", "'name"] {
        let source = format!("x::123{name}");
        let (green, records, exit, remainder) = parse(&source, 0, 0, None, None);
        assert_eq!(
            records,
            [record(
                ExpressionRole::PathSegment,
                RecoveryKind::Error,
                3..6
            )]
        );
        assert_eq!(green.to_string(), "x::123");
        let NormalizedExit::Complete(Err(Either::Left(item)), LineEntry::InLine) = exit else {
            panic!("sigil retry stays current")
        };
        assert_eq!(token_kind(&item), Some(TokenKind::SigilIdentifier));
        assert_eq!(item.payload_view().spelling(), Some(name));
        assert_eq!(item.extent(source.len()).recovery_range(), 6..source.len());
        assert_eq!(remainder, "");
    }
}

#[test]
fn fixed_tail_boundaries_keep_the_whole_item_before_and_after_error() {
    use crate::lexical::stops::{STOP_COMMA, STOP_LINE_BREAK};
    for (intro, role, bad) in [
        ("x.", ExpressionRole::FieldName, "@"),
        ("x::", ExpressionRole::PathSegment, "123"),
    ] {
        for (boundary, stops, kind) in [
            (",", STOP_COMMA, TokenKind::Comma),
            (":", STOP_COLON, TokenKind::Colon),
            (")", 0, TokenKind::RParen),
            ("]", 0, TokenKind::RBracket),
            ("}", 0, TokenKind::RBrace),
            ("else", STOP_ELSE, TokenKind::Identifier),
            (" else", STOP_ELSE, TokenKind::Identifier),
            ("\r\nname", STOP_LINE_BREAK, TokenKind::Identifier),
        ] {
            for malformed in ["", bad] {
                let source = format!("{intro}{malformed}{boundary}");
                let (green, records, exit, remainder) = parse(&source, stops, 40, None, None);
                let start = 40 + intro.len();
                let end = start + malformed.len();
                assert_eq!(
                    records,
                    [record(
                        role,
                        if malformed.is_empty() {
                            RecoveryKind::Missing
                        } else {
                            RecoveryKind::Error
                        },
                        start..end
                    )],
                    "{source:?}"
                );
                assert_eq!(green.to_string(), format!("{intro}{malformed}"));
                let NormalizedExit::Complete(Err(Either::Left(item)), _) = exit else {
                    panic!("protected Item remains current: {source:?}")
                };
                assert_eq!(token_kind(&item), Some(kind));
                assert_eq!(
                    item.extent(40 + source.len()).recovery_range(),
                    end..40 + source.len()
                );
                assert_eq!(remainder, "");
            }
        }
    }
}

#[test]
fn accepted_path_leading_and_names_remain_in_the_tail() {
    for source in [
        "x.foo::bar",
        "x:: $name",
        "x::\r\nname",
        "x::\n  &name",
        "x::'name",
    ] {
        let (green, records, _, _) = parse(source, 0, 0, None, None);
        assert_eq!(green.to_string(), source);
        assert!(records.is_empty());
    }
}

#[test]
fn recovered_names_keep_fixed_and_unstopped_colon_continuations() {
    for (source, role, range) in [
        ("x.@: y", ExpressionRole::FieldName, 2..3),
        ("x::123: y", ExpressionRole::PathSegment, 3..6),
        ("x.@.field", ExpressionRole::FieldName, 2..3),
        ("x::123::name", ExpressionRole::PathSegment, 3..6),
    ] {
        let (green, records, _, _) = parse(source, 0, 0, None, None);
        assert_eq!(records, [record(role, RecoveryKind::Error, range)]);
        assert_eq!(green.to_string(), source);
    }
}

#[test]
fn fixed_tail_utf8_error_and_quoted_fence_have_physical_extents() {
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
    for (source, role, kind, range, emitted) in [
        (
            "x.\r\n> > ```\nouter",
            ExpressionRole::FieldName,
            RecoveryKind::Missing,
            104..104,
            "x.",
        ),
        (
            "x::💥\r\n> > ```\nouter",
            ExpressionRole::PathSegment,
            RecoveryKind::Error,
            103..107,
            "x::💥",
        ),
    ] {
        let (green, records, exit, remainder) = parse(source, 0, 100, Some(&fence), None);
        assert_eq!(records, [record(role, kind, range)]);
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
}

#[test]
fn fixed_tail_recovery_keeps_threshold_ml_and_seeded_output() {
    let operators = OperatorTable::from_declarations([OperatorDeclaration::new(
        "+",
        OperatorFixities::new().with_infix(BindingPower::scalar(20), BindingPower::scalar(21)),
    )])
    .unwrap();
    for (source, threshold, mode, expected_text, pending, range) in [
        (
            "x.@ + y",
            70,
            MlMode::All,
            "x.@",
            Some(TokenKind::Operator),
            2..3,
        ),
        ("x.@ + y", 0, MlMode::All, "x.@ + y", None, 2..3),
        (
            "x::123 name",
            0,
            MlMode::None,
            "x::123",
            Some(TokenKind::Identifier),
            3..6,
        ),
        ("x::123 name", 0, MlMode::All, "x::123 name", None, 3..6),
    ] {
        let mut input = source;
        let mut recover = Recover::new_for_test(&operators);
        let mut output = GreenNodeBuilder::new();
        output.start_node(SyntaxKind::Root.into());
        output.token(SyntaxKind::Identifier.into(), "seed");
        let threshold = BindingPower::scalar(threshold);
        let exit = expr_normalized(
            crate::cursor::SyntaxIn::new(&mut input, &mut recover, &mut output),
            Some(&threshold),
            0,
            0,
            mode,
            StatementLineHandoff::OrdinaryLayout,
            0,
            LineEntry::InLine,
            None,
            Some(AmbientClaimView::root_statement(0)).into(),
            None,
        )
        .unwrap();
        output.finish_node();
        let (green, records) = (output.finish(), recover.finish_recoveries_for_test());
        assert_eq!(green.to_string(), format!("seed{expected_text}"));
        assert_eq!(
            records,
            [record(
                if source.starts_with("x.") {
                    ExpressionRole::FieldName
                } else {
                    ExpressionRole::PathSegment
                },
                RecoveryKind::Error,
                range
            )]
        );
        if let Some(kind) = pending {
            let NormalizedExit::Complete(Err(Either::Left(item)), _) = exit else {
                panic!("same Item handoff")
            };
            assert_eq!(token_kind(&item), Some(kind));
            if kind == TokenKind::Operator {
                assert_eq!(input, " y");
            }
        }
    }
}

fn commit_seed(output: &mut GreenNodeBuilder<'_>, recover: &mut Recover) {
    use crate::cursor::recovery::RecoveryDraft;
    let seed = record(ExpressionRole::FieldName, RecoveryKind::Missing, 0..0);
    output.start_node(SyntaxKind::Missing.into());
    output.finish_node();
    recover.commit_recovery_for_test(RecoveryDraft::new(
        seed.site,
        seed.kind,
        seed.unexpected,
        seed.expectations,
        seed.primary_expectation,
    ));
}

#[test]
fn fixed_tail_recovery_allocates_after_committed_and_frozen_records() {
    for (source, role, range) in [
        ("x.@", ExpressionRole::FieldName, 12..13),
        ("x::123", ExpressionRole::PathSegment, 13..16),
    ] {
        let mut seed = record(ExpressionRole::FieldName, RecoveryKind::Missing, 0..0);
        seed.id = DiagnosticId(7);
        let mut reused = record(role, RecoveryKind::Error, range.clone());
        reused.id = DiagnosticId(19);
        let frozen = [seed, reused];
        for reconcile in [false, true] {
            let operators = OperatorTable::empty();
            let mut recover = Recover::new_for_test(&operators);
            let mut output = if reconcile {
                {
                    recover = Recover::reconcile_for_test(recover.operators(), &frozen);
                    GreenNodeBuilder::new()
                }
            } else {
                GreenNodeBuilder::new()
            };
            output.start_node(SyntaxKind::Root.into());
            commit_seed(&mut output, &mut recover);
            assert_eq!(recover.recovery_slot_count(), 1);
            for origin in [10, 20] {
                let mut input = source;
                let exit = expr_normalized(
                    crate::cursor::SyntaxIn::new(&mut input, &mut recover, &mut output),
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
                assert!(matches!(
                    exit,
                    NormalizedExit::Complete(Err(Either::Right(_)), _)
                ));
            }
            assert_eq!(
                recover.diagnostic_position(),
                if reconcile {
                    (Some(21), 2)
                } else {
                    (Some(3), 0)
                }
            );
            output.finish_node();
            let (green, records) = (output.finish(), recover.finish_recoveries_for_test());
            assert_eq!(green.to_string(), source.repeat(2));
            let mut expected = [
                record(ExpressionRole::FieldName, RecoveryKind::Missing, 0..0),
                record(role, RecoveryKind::Error, range.clone()),
                record(role, RecoveryKind::Error, range.start + 10..range.end + 10),
            ];
            for (record, id) in
                expected
                    .iter_mut()
                    .zip(if reconcile { [7, 19, 20] } else { [0, 1, 2] })
            {
                record.id = DiagnosticId(id);
            }
            assert_eq!(records, expected);
        }
    }
}

#[test]
fn rejected_or_line_deferred_fixed_tail_preserves_seeded_output_and_cursor() {
    use crate::lexical::stops::STOP_LINE_BREAK;
    use crate::{expression::tail_normalized, lexical::expression_item::expression_item};
    let mut seed = record(ExpressionRole::FieldName, RecoveryKind::Missing, 0..0);
    seed.id = DiagnosticId(7);
    let mut next = record(ExpressionRole::FieldName, RecoveryKind::Missing, 12..12);
    next.id = DiagnosticId(19);
    let frozen = [seed, next];
    for (source, stops, kind) in [
        ("..rest", 0, TokenKind::Unknown),
        ("\n.field", STOP_LINE_BREAK, TokenKind::Dot),
        ("\n::name", STOP_LINE_BREAK, TokenKind::PathSeparator),
    ] {
        let mut control = None;
        let mut control_item = None;
        for attempt in [false, true] {
            let operators = OperatorTable::empty();
            let mut recover = Recover::new_for_test(&operators);
            let mut output = {
                recover = Recover::reconcile_for_test(recover.operators(), &frozen);
                GreenNodeBuilder::new()
            };
            output.start_node(SyntaxKind::Root.into());
            output.token(SyntaxKind::Identifier.into(), "seed");
            commit_seed(&mut output, &mut recover);
            let mut input = source;
            let (item, origin, line) = expression_item(
                crate::cursor::SyntaxIn::new(&mut input, &mut recover, &mut output),
                OperatorSite::Led,
                0,
                LineEntry::InLine,
                None,
                0,
                stops,
            );
            assert_eq!(token_kind(&item), Some(kind));
            let remainder = input;
            let position = recover.diagnostic_position();
            if attempt {
                let exit = tail_normalized(
                    crate::cursor::SyntaxIn::new(&mut input, &mut recover, &mut output),
                    item,
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
                let NormalizedExit::Complete(Err(Either::Left(item)), returned_line) = exit else {
                    panic!("fixed-tail entry must remain unread")
                };
                assert_eq!(&item, control_item.as_ref().unwrap());
                assert_eq!(returned_line, line);
            } else {
                control_item = Some(item);
            }
            assert_eq!(input, remainder);
            assert_eq!(recover.diagnostic_position(), position);
            assert_eq!(recover.recovery_slot_count(), 1);
            let mut input = "x.";
            expr_normalized(
                crate::cursor::SyntaxIn::new(&mut input, &mut recover, &mut output),
                None,
                0,
                0,
                MlMode::All,
                StatementLineHandoff::OrdinaryLayout,
                10,
                LineEntry::InLine,
                None,
                Some(AmbientClaimView::root_statement(0)).into(),
                None,
            )
            .unwrap();
            assert_eq!(recover.diagnostic_position(), (Some(20), 2));
            output.finish_node();
            let product = (output.finish(), recover.finish_recoveries_for_test());
            assert_eq!(product.0.to_string(), "seedx.");
            assert_eq!(product.1, frozen);
            if let Some(control) = &control {
                assert_eq!(&product, control);
            } else {
                control = Some(product);
            }
        }
    }
}
