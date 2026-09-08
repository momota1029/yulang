use crate::recovery_record::{CastRole, RecoveryKind};
use crate::tests::support::*;

fn declaration(green: &GreenNode) -> SyntaxNode {
    SyntaxNode::new_root(green.clone())
        .descendants()
        .find(|node| node.kind() == SyntaxKind::CastDeclaration)
        .expect("CastDeclaration")
}

fn count(node: &SyntaxNode, kind: SyntaxKind) -> usize {
    node.descendants()
        .filter(|node| node.kind() == kind)
        .count()
}

fn token_count(node: &SyntaxNode, kind: SyntaxKind) -> usize {
    node.descendants_with_tokens()
        .filter_map(|element| element.into_token())
        .filter(|token| token.kind() == kind)
        .count()
}

fn pending_item(exit: Option<NormalizedExit>) -> Item {
    match exit {
        Some(NormalizedExit::Complete(Err(Either::Left(item)), _)) => item,
        Some(NormalizedExit::Complete(Err(Either::Right(end)), _)) => end.item,
        _ => panic!("Cast witness must return one pending Item"),
    }
}

fn typed_cast<'s, 'frozen>(
    source: &'s str,
    origin: usize,
    frozen: Option<&'frozen [CommittedRecoveryRecord]>,
    stops: Stops,
    fence: Option<&FenceBoundary>,
) -> (
    GreenNode,
    Option<NormalizedExit>,
    Vec<CommittedRecoveryRecord>,
    &'s str,
) {
    typed_cast_at(source, origin, frozen, stops, LineEntry::InLine, fence)
}

fn typed_cast_at<'s, 'frozen>(
    source: &'s str,
    origin: usize,
    frozen: Option<&'frozen [CommittedRecoveryRecord]>,
    stops: Stops,
    line_entry: LineEntry,
    fence: Option<&FenceBoundary>,
) -> (
    GreenNode,
    Option<NormalizedExit>,
    Vec<CommittedRecoveryRecord>,
    &'s str,
) {
    let operators = OperatorTable::empty();
    let mut input = source;
    let mut recover = Recover::new(&operators);
    let mut builder = frozen.map_or_else(GreenNodeBuilder::new, GreenNodeBuilder::reconcile);
    builder.start_node(SyntaxKind::Root.into());
    let exit = cast_declaration_witness(
        In::new(&mut input, &mut recover, &mut builder),
        0,
        stops,
        crate::statement::StatementLineHandoff::OrdinaryLayout,
        origin,
        line_entry,
        fence,
    );
    builder.finish_node();
    let (green, records) = builder.finish_with_recoveries();
    (green, exit, records, input)
}

fn pattern_introducer_record(
    id: u32,
    kind: RecoveryKind,
    range: std::ops::Range<usize>,
) -> CommittedRecoveryRecord {
    use crate::recovery_record::{
        DeclarationRole, Delimiter, DiagnosticId, ExpectationSources, ExpectedSyntax, GrammarRole,
        PunctuationEvidence, RecoverySiteKey, SyntaxExpectation, UnexpectedCategory,
        UnexpectedSyntax,
    };
    use std::sync::Arc;

    let role = GrammarRole::Declaration(DeclarationRole::Cast(CastRole::PatternIntroducer));
    let unexpected = if kind == RecoveryKind::Error {
        Arc::from([UnexpectedSyntax::Token {
            range: range.clone(),
            category: UnexpectedCategory::OtherCharacter,
        }])
    } else {
        Arc::from([])
    };
    CommittedRecoveryRecord {
        id: DiagnosticId(id),
        site: RecoverySiteKey {
            role,
            range: range.clone(),
        },
        kind,
        unexpected,
        expectations: Arc::from([SyntaxExpectation {
            role,
            expected: ExpectedSyntax::Punctuation(PunctuationEvidence::Open(
                Delimiter::Parenthesis,
            )),
            range,
            sources: ExpectationSources::COMMITTED_RECOVERY_RULE,
        }]),
        primary_expectation: 0,
    }
}

fn cast_pattern_record(id: u32, at: usize) -> CommittedRecoveryRecord {
    use crate::recovery_record::{
        DeclarationRole, DiagnosticId, ExpectationSources, ExpectedSyntax, GrammarRole,
        RecoverySiteKey, SyntaxExpectation,
    };
    use std::sync::Arc;

    let role = GrammarRole::Declaration(DeclarationRole::Cast(CastRole::Pattern));
    let range = at..at;
    CommittedRecoveryRecord {
        id: DiagnosticId(id),
        site: RecoverySiteKey {
            role,
            range: range.clone(),
        },
        kind: RecoveryKind::Missing,
        unexpected: Arc::from([]),
        expectations: Arc::from([SyntaxExpectation {
            role,
            expected: ExpectedSyntax::Pattern,
            range,
            sources: ExpectationSources::COMMITTED_RECOVERY_RULE,
        }]),
        primary_expectation: 0,
    }
}

fn cast_pattern_close_record(
    id: u32,
    kind: RecoveryKind,
    range: std::ops::Range<usize>,
) -> CommittedRecoveryRecord {
    use crate::recovery_record::{
        ConstructRole, Delimiter, DiagnosticId, ExpectationSources, ExpectedSyntax, GrammarRole,
        PunctuationEvidence, RecoverySiteKey, SyntaxExpectation, UnexpectedCategory,
        UnexpectedSyntax,
    };
    use std::sync::Arc;
    let role = GrammarRole::ClosingDelimiter {
        owner: ConstructRole::CastPattern,
        delimiter: Delimiter::Parenthesis,
    };
    let unexpected = (kind == RecoveryKind::Error)
        .then(|| UnexpectedSyntax::Token {
            range: range.clone(),
            category: UnexpectedCategory::OtherCharacter,
        })
        .into_iter()
        .collect::<Vec<_>>()
        .into();
    CommittedRecoveryRecord {
        id: DiagnosticId(id),
        site: RecoverySiteKey {
            role,
            range: range.clone(),
        },
        kind,
        unexpected,
        expectations: Arc::from([SyntaxExpectation {
            role,
            expected: ExpectedSyntax::Punctuation(PunctuationEvidence::Close(
                Delimiter::Parenthesis,
            )),
            range,
            sources: ExpectationSources::COMMITTED_RECOVERY_RULE,
        }]),
        primary_expectation: 0,
    }
}

fn cast_target_introducer_record(
    id: u32,
    kind: RecoveryKind,
    range: std::ops::Range<usize>,
) -> CommittedRecoveryRecord {
    use crate::recovery_record::{
        DeclarationRole, DiagnosticId, ExpectationSources, ExpectedSyntax, GrammarRole,
        PunctuationEvidence, RecoverySiteKey, SyntaxExpectation, UnexpectedCategory,
        UnexpectedSyntax,
    };
    use std::sync::Arc;
    let role = GrammarRole::Declaration(DeclarationRole::Cast(CastRole::TargetIntroducer));
    let unexpected = (kind == RecoveryKind::Error)
        .then(|| UnexpectedSyntax::Token {
            range: range.clone(),
            category: UnexpectedCategory::OtherCharacter,
        })
        .into_iter()
        .collect::<Vec<_>>()
        .into();
    CommittedRecoveryRecord {
        id: DiagnosticId(id),
        site: RecoverySiteKey {
            role,
            range: range.clone(),
        },
        kind,
        unexpected,
        expectations: Arc::from([SyntaxExpectation {
            role,
            expected: ExpectedSyntax::Punctuation(PunctuationEvidence::Colon),
            range,
            sources: ExpectationSources::COMMITTED_RECOVERY_RULE,
        }]),
        primary_expectation: 0,
    }
}

fn cast_body_introducer_record(
    id: u32,
    kind: RecoveryKind,
    range: std::ops::Range<usize>,
) -> CommittedRecoveryRecord {
    use crate::recovery_record::{
        DeclarationRole, DiagnosticId, ExpectationSources, ExpectedSyntax, GrammarRole,
        PunctuationEvidence, RecoverySiteKey, SyntaxExpectation, UnexpectedCategory,
        UnexpectedSyntax,
    };
    use std::sync::Arc;
    let role = GrammarRole::Declaration(DeclarationRole::Cast(CastRole::BodyIntroducer));
    let unexpected = (kind == RecoveryKind::Error)
        .then(|| UnexpectedSyntax::Token {
            range: range.clone(),
            category: UnexpectedCategory::OtherCharacter,
        })
        .into_iter()
        .collect::<Vec<_>>()
        .into();
    CommittedRecoveryRecord {
        id: DiagnosticId(id),
        site: RecoverySiteKey {
            role,
            range: range.clone(),
        },
        kind,
        unexpected,
        expectations: Arc::from([SyntaxExpectation {
            role,
            expected: ExpectedSyntax::Punctuation(PunctuationEvidence::Semicolon),
            range,
            sources: ExpectationSources::COMMITTED_RECOVERY_RULE,
        }]),
        primary_expectation: 0,
    }
}

fn cast_body_record(
    id: u32,
    kind: RecoveryKind,
    range: std::ops::Range<usize>,
) -> CommittedRecoveryRecord {
    use crate::recovery_record::{
        DeclarationRole, DiagnosticId, ExpectationSources, ExpectedSyntax, GrammarRole,
        RecoverySiteKey, SyntaxExpectation, UnexpectedCategory, UnexpectedSyntax,
    };
    use std::sync::Arc;
    let role = GrammarRole::Declaration(DeclarationRole::Cast(CastRole::Body));
    let unexpected = (kind == RecoveryKind::Error)
        .then(|| UnexpectedSyntax::Token {
            range: range.clone(),
            category: UnexpectedCategory::OtherCharacter,
        })
        .into_iter()
        .collect::<Vec<_>>()
        .into();
    CommittedRecoveryRecord {
        id: DiagnosticId(id),
        site: RecoverySiteKey {
            role,
            range: range.clone(),
        },
        kind,
        unexpected,
        expectations: Arc::from([SyntaxExpectation {
            role,
            expected: ExpectedSyntax::Expression,
            range,
            sources: ExpectationSources::COMMITTED_RECOVERY_RULE,
        }]),
        primary_expectation: 0,
    }
}

#[test]
fn cast_body_records_are_exact_and_reconcile() {
    for origin in [100, 12_000] {
        for (source, stops, kind, relative_range) in [
            ("cast(x): A =", 0, RecoveryKind::Missing, 12..12),
            ("cast(x): A =   ", 0, RecoveryKind::Missing, 15..15),
            ("cast(x): A = ;", 0, RecoveryKind::Missing, 12..12),
            ("cast(x): A = ,", 0, RecoveryKind::Missing, 12..12),
            ("cast(x): A = )", 0, RecoveryKind::Missing, 12..12),
            ("cast(x): A = ]", 0, RecoveryKind::Missing, 12..12),
            ("cast(x): A = }", 0, RecoveryKind::Missing, 12..12),
            ("cast(x): A =\r\nnext", 0, RecoveryKind::Missing, 12..12),
            (
                "cast(x): A = else",
                STOP_ELSE,
                RecoveryKind::Missing,
                12..12,
            ),
            ("cast(x): A = @ value", 0, RecoveryKind::Error, 13..14),
            ("cast(x): A = @ )", 0, RecoveryKind::Error, 13..14),
            ("cast(x): A = @ 💥 value", 0, RecoveryKind::Error, 13..19),
            ("cast(x): A = @   ", 0, RecoveryKind::Error, 13..17),
            ("cast(x): A = @\r\n", 0, RecoveryKind::Error, 13..14),
        ] {
            let expected = cast_body_record(
                0,
                kind,
                origin + relative_range.start..origin + relative_range.end,
            );
            let (green, _, records, remainder) = typed_cast(source, origin, None, stops, None);
            assert_eq!(records.first(), Some(&expected), "{source:?} at {origin}");
            assert_eq!(
                records
                    .iter()
                    .filter(|record| {
                        record.site.role
                            == crate::recovery_record::GrammarRole::Declaration(
                                crate::recovery_record::DeclarationRole::Cast(CastRole::Body),
                            )
                    })
                    .collect::<Vec<_>>(),
                [&expected],
                "{source:?} at {origin}"
            );
            let (again, _, frozen, frozen_remainder) =
                typed_cast(source, origin, Some(&records), stops, None);
            assert_eq!(again, green, "{source:?} at {origin}");
            assert_eq!(frozen, records, "{source:?} at {origin}");
            assert_eq!(frozen_remainder, remainder, "{source:?} at {origin}");
            let mut seeded = records.clone();
            seeded[0].id = crate::recovery_record::DiagnosticId(71);
            let (seeded_green, _, seeded_records, seeded_remainder) =
                typed_cast(source, origin, Some(&seeded), stops, None);
            assert_eq!(seeded_green, green, "{source:?} at {origin}");
            assert_eq!(seeded_records, seeded, "{source:?} at {origin}");
            assert_eq!(seeded_remainder, remainder, "{source:?} at {origin}");
        }
    }
}

#[test]
fn cast_body_introducer_records_are_exact_and_reconcile() {
    for origin in [100, 12_000] {
        for (source, stops, kind, relative_range) in [
            ("cast(x): A", 0, RecoveryKind::Missing, 10..10),
            ("cast(x): A )", 0, RecoveryKind::Missing, 10..10),
            ("cast(x): A ]", 0, RecoveryKind::Missing, 10..10),
            ("cast(x): A }", 0, RecoveryKind::Missing, 10..10),
            ("cast(x): A ,", 0, RecoveryKind::Missing, 10..10),
            ("cast(x): A\r\nvalue", 0, RecoveryKind::Missing, 10..10),
            ("cast(x): A else", STOP_ELSE, RecoveryKind::Missing, 10..10),
            ("cast(x): A @ ;", 0, RecoveryKind::Error, 11..12),
            ("cast(x): A @ = value", 0, RecoveryKind::Error, 11..12),
            ("cast(x): A @ # = value", 0, RecoveryKind::Error, 11..14),
            ("cast(x): A @ )", 0, RecoveryKind::Error, 11..12),
            ("cast(x): A @   ", 0, RecoveryKind::Error, 11..15),
            ("cast(x): A @\r\n", 0, RecoveryKind::Error, 11..12),
            ("cast(x): A @ あ ;", 0, RecoveryKind::Error, 11..16),
        ] {
            let expected = cast_body_introducer_record(
                0,
                kind,
                origin + relative_range.start..origin + relative_range.end,
            );
            let (green, _, records, remainder) = typed_cast(source, origin, None, stops, None);
            assert_eq!(records.first(), Some(&expected), "{source:?} at {origin}");
            assert_eq!(
                records
                    .iter()
                    .filter(|record| {
                        record.site.role
                            == crate::recovery_record::GrammarRole::Declaration(
                                crate::recovery_record::DeclarationRole::Cast(
                                    CastRole::BodyIntroducer,
                                ),
                            )
                    })
                    .collect::<Vec<_>>(),
                [&expected],
                "{source:?} at {origin}"
            );
            let (again, _, frozen, frozen_remainder) =
                typed_cast(source, origin, Some(&records), stops, None);
            assert_eq!(again, green, "{source:?} at {origin}");
            assert_eq!(frozen, records, "{source:?} at {origin}");
            assert_eq!(frozen_remainder, remainder, "{source:?} at {origin}");
            let mut seeded = records.clone();
            seeded[0].id = crate::recovery_record::DiagnosticId(71);
            let (seeded_green, _, seeded_records, seeded_remainder) =
                typed_cast(source, origin, Some(&seeded), stops, None);
            assert_eq!(seeded_green, green, "{source:?} at {origin}");
            assert_eq!(seeded_records, seeded, "{source:?} at {origin}");
            assert_eq!(seeded_remainder, remainder, "{source:?} at {origin}");
        }
    }
}

#[test]
fn cast_target_introducer_records_are_exact_and_reconcile() {
    for origin in [100, 12_000] {
        for (source, stops, kind, relative_range) in [
            ("cast(x)", 0, RecoveryKind::Missing, 7..7),
            ("cast(x);", 0, RecoveryKind::Missing, 7..7),
            ("cast(x)= value", 0, RecoveryKind::Missing, 7..7),
            ("cast(x) T;", 0, RecoveryKind::Missing, 8..8),
            ("cast(x) )", 0, RecoveryKind::Missing, 7..7),
            ("cast(x) ]", 0, RecoveryKind::Missing, 7..7),
            ("cast(x) }", 0, RecoveryKind::Missing, 7..7),
            ("cast(x)\r\nT;", 0, RecoveryKind::Missing, 7..7),
            ("cast(x) else", STOP_ELSE, RecoveryKind::Missing, 7..7),
            ("cast(x) @ : T;", 0, RecoveryKind::Error, 8..9),
            ("cast(x) @ T;", 0, RecoveryKind::Error, 8..9),
            ("cast(x) @ ;", 0, RecoveryKind::Error, 8..9),
            ("cast(x) @ = value", 0, RecoveryKind::Error, 8..9),
            ("cast(x) @ )", 0, RecoveryKind::Error, 8..9),
            ("cast(x) @   ", 0, RecoveryKind::Error, 8..12),
            ("cast(x) @\r\n", 0, RecoveryKind::Error, 8..9),
            ("cast(x) @ あ T;", 0, RecoveryKind::Error, 8..9),
        ] {
            let expected = cast_target_introducer_record(
                0,
                kind,
                origin + relative_range.start..origin + relative_range.end,
            );
            let (green, _, records, remainder) = typed_cast(source, origin, None, stops, None);
            assert_eq!(records.first(), Some(&expected), "{source:?} at {origin}");
            assert_eq!(
                records
                    .iter()
                    .filter(|record| {
                        record.site.role
                            == crate::recovery_record::GrammarRole::Declaration(
                                crate::recovery_record::DeclarationRole::Cast(
                                    CastRole::TargetIntroducer,
                                ),
                            )
                    })
                    .collect::<Vec<_>>(),
                [&expected],
                "{source:?} at {origin}"
            );
            let (again, _, frozen, frozen_remainder) =
                typed_cast(source, origin, Some(&records), stops, None);
            assert_eq!(again, green, "{source:?} at {origin}");
            assert_eq!(frozen, records, "{source:?} at {origin}");
            assert_eq!(frozen_remainder, remainder, "{source:?} at {origin}");
            let mut seeded = records.clone();
            seeded[0].id = crate::recovery_record::DiagnosticId(71);
            let (seeded_green, _, seeded_records, seeded_remainder) =
                typed_cast(source, origin, Some(&seeded), stops, None);
            assert_eq!(seeded_green, green, "{source:?} at {origin}");
            assert_eq!(seeded_records, seeded, "{source:?} at {origin}");
            assert_eq!(seeded_remainder, remainder, "{source:?} at {origin}");
        }
    }
}

#[test]
fn cast_pattern_close_records_are_exact_and_reconcile() {
    for origin in [100, 12_000] {
        for (source, kind, relative_range) in [
            ("cast(x", RecoveryKind::Missing, 6..6),
            ("cast(x;", RecoveryKind::Missing, 6..6),
            ("cast(x= value", RecoveryKind::Missing, 6..6),
            ("cast(x @ ): T;", RecoveryKind::Error, 7..8),
            ("cast(x @   ", RecoveryKind::Error, 7..11),
            ("cast(x @\r\n", RecoveryKind::Error, 7..8),
        ] {
            let expected = cast_pattern_close_record(
                0,
                kind,
                origin + relative_range.start..origin + relative_range.end,
            );
            let (green, _, records, remainder) = typed_cast(source, origin, None, 0, None);
            assert_eq!(records.first(), Some(&expected), "{source:?} at {origin}");
            assert_eq!(
                records
                    .iter()
                    .filter(|record| {
                        record.site.role
                            == crate::recovery_record::GrammarRole::ClosingDelimiter {
                                owner: crate::recovery_record::ConstructRole::CastPattern,
                                delimiter: crate::recovery_record::Delimiter::Parenthesis,
                            }
                    })
                    .collect::<Vec<_>>(),
                [&expected],
                "{source:?} at {origin}"
            );
            let (again, _, frozen, frozen_remainder) =
                typed_cast(source, origin, Some(&records), 0, None);
            assert_eq!(again, green, "{source:?} at {origin}");
            assert_eq!(frozen, records, "{source:?} at {origin}");
            assert_eq!(frozen_remainder, remainder, "{source:?} at {origin}");
            let mut seeded = records.clone();
            seeded[0].id = crate::recovery_record::DiagnosticId(71);
            let (seeded_green, _, seeded_records, seeded_remainder) =
                typed_cast(source, origin, Some(&seeded), 0, None);
            assert_eq!(seeded_green, green, "{source:?} at {origin}");
            assert_eq!(seeded_records, seeded, "{source:?} at {origin}");
            assert_eq!(seeded_remainder, remainder, "{source:?} at {origin}");
        }
    }
}

#[test]
fn cast_pattern_absence_records_are_exact_and_reconcile() {
    for origin in [100, 12_000] {
        for source in [
            "cast(",
            "cast(\r\n",
            "cast()",
            "cast(: T;",
            "cast(;",
            "cast(= value",
        ] {
            let mut expected = vec![cast_pattern_record(0, origin + 5)];
            if source == "cast()" {
                expected.push(cast_target_introducer_record(
                    1,
                    RecoveryKind::Missing,
                    origin + 6..origin + 6,
                ));
            }
            let (green, _, records, remainder) = typed_cast(source, origin, None, 0, None);
            assert_eq!(records, expected, "{source:?} at {origin}");
            let (again, _, frozen, frozen_remainder) =
                typed_cast(source, origin, Some(&records), 0, None);
            assert_eq!(again, green, "{source:?} at {origin}");
            assert_eq!(frozen, records, "{source:?} at {origin}");
            assert_eq!(frozen_remainder, remainder, "{source:?} at {origin}");

            let mut seeded = records.clone();
            seeded[0].id = crate::recovery_record::DiagnosticId(71);
            let (seeded_green, _, seeded_records, seeded_remainder) =
                typed_cast(source, origin, Some(&seeded), 0, None);
            assert_eq!(seeded_green, green, "{source:?} at {origin}");
            assert_eq!(seeded_records, seeded, "{source:?} at {origin}");
            assert_eq!(seeded_remainder, remainder, "{source:?} at {origin}");
        }
    }
}

#[test]
fn cast_pattern_introducer_records_are_exact_shifted_and_reconciled() {
    for origin in [100, 12_000] {
        for (source, stops, kind, relative_range) in [
            ("cast", 0, RecoveryKind::Missing, 4..4),
            ("cast x", 0, RecoveryKind::Missing, 5..5),
            ("cast;", 0, RecoveryKind::Missing, 4..4),
            ("cast: T;", 0, RecoveryKind::Missing, 4..4),
            ("cast= x", 0, RecoveryKind::Missing, 4..4),
            ("cast )", 0, RecoveryKind::Missing, 4..4),
            ("cast else tail", STOP_ELSE, RecoveryKind::Missing, 4..4),
            ("cast @", 0, RecoveryKind::Error, 5..6),
            ("cast @ x", 0, RecoveryKind::Error, 5..6),
            ("cast @ # x", 0, RecoveryKind::Error, 5..8),
            ("cast @ (x): T;", 0, RecoveryKind::Error, 5..6),
            ("cast @ : T;", 0, RecoveryKind::Error, 5..6),
            ("cast @ = x", 0, RecoveryKind::Error, 5..6),
            ("cast @ )", 0, RecoveryKind::Error, 5..6),
            ("cast @   ", 0, RecoveryKind::Error, 5..9),
            ("cast @\r\n", 0, RecoveryKind::Error, 5..6),
            ("cast @ あ x", 0, RecoveryKind::Error, 5..6),
        ] {
            let range = origin + relative_range.start..origin + relative_range.end;
            let mut expected = vec![pattern_introducer_record(0, kind, range)];
            if source == "cast @ あ x" {
                expected.push(cast_target_introducer_record(
                    1,
                    RecoveryKind::Missing,
                    origin + 11..origin + 11,
                ));
                expected.push(cast_body_introducer_record(
                    2,
                    RecoveryKind::Missing,
                    origin + 12..origin + 12,
                ));
            }
            let (green, _, records, remainder) = typed_cast(source, origin, None, stops, None);
            assert_eq!(records, expected, "{source:?} at {origin}");
            let (again, _, frozen, frozen_remainder) =
                typed_cast(source, origin, Some(&records), stops, None);
            assert_eq!(again, green, "{source:?} at {origin}");
            assert_eq!(frozen, records, "{source:?} at {origin}");
            assert_eq!(frozen_remainder, remainder, "{source:?} at {origin}");

            let mut seeded = records.clone();
            seeded[0].id = crate::recovery_record::DiagnosticId(71);
            let (seeded_green, _, seeded_records, seeded_remainder) =
                typed_cast(source, origin, Some(&seeded), stops, None);
            assert_eq!(seeded_green, green, "{source:?} at {origin}");
            assert_eq!(seeded_records, seeded, "{source:?} at {origin}");
            assert_eq!(seeded_remainder, remainder, "{source:?} at {origin}");
        }
    }
}

#[test]
fn cast_private_owner_builds_bodyless_inline_and_indented_forms() {
    for (source, body, indented) in [
        ("cast(x: A): B;", 0, 0),
        ("pub cast(x: A): B = x", 1, 0),
        ("cast(x: A): B =\n  x", 1, 1),
    ] {
        let (green, exit, remainder) = run_cast_declaration(source, 0, 0, LineEntry::InLine, None);
        assert!(exit.is_some(), "{source:?}");
        assert_eq!(green.to_string(), source, "{source:?}");
        assert_eq!(remainder, "", "{source:?}");
        let declaration = declaration(&green);
        assert_eq!(
            count(&declaration, SyntaxKind::CastPattern),
            1,
            "{source:?}"
        );
        assert_eq!(count(&declaration, SyntaxKind::CastTarget), 1, "{source:?}");
        assert_eq!(
            count(&declaration, SyntaxKind::CastBody),
            body,
            "{source:?}"
        );
        assert_eq!(
            count(&declaration, SyntaxKind::IndentedStatementBlock),
            indented,
            "{source:?}"
        );
        assert_eq!(count(&declaration, SyntaxKind::Missing), 0, "{source:?}");
        assert_eq!(count(&declaration, SyntaxKind::Error), 0, "{source:?}");
    }

    let source = "pub cast(x: int): user_id = user_id { raw: x }";
    let (green, _, remainder) = run_cast_declaration(source, 0, 0, LineEntry::InLine, None);
    assert_eq!(green.to_string(), source);
    assert_eq!(remainder, "");
    let declaration = declaration(&green);
    assert_eq!(count(&declaration, SyntaxKind::CastBody), 1);
    assert!(count(&declaration, SyntaxKind::OperatorChain) >= 1);
    assert_eq!(
        count(&declaration, SyntaxKind::BracedStatementBlockExpression),
        1
    );
    assert_eq!(count(&declaration, SyntaxKind::Missing), 0);
    assert_eq!(count(&declaration, SyntaxKind::Error), 0);
    assert_eq!(
        declaration
            .children_with_tokens()
            .map(|element| element.kind())
            .collect::<Vec<_>>(),
        [
            SyntaxKind::PubKw,
            SyntaxKind::Whitespace,
            SyntaxKind::CastKw,
            SyntaxKind::CastPattern,
            SyntaxKind::CastTarget,
            SyntaxKind::Whitespace,
            SyntaxKind::Equals,
            SyntaxKind::CastBody,
        ]
    );
}

#[test]
fn cast_intro_is_exact_visibility_aware_and_uses_canonical_statement_dispatch() {
    for source in [
        "cast(x): T;",
        "my cast(x): T;",
        "our cast (x): T;",
        "pub cast(x): T;",
        "pub\n  cast\n    (x): T;",
    ] {
        let (green, exit, _) = run_cast_declaration(source, 0, 0, LineEntry::InLine, None);
        assert!(exit.is_some(), "{source:?}");
        assert_eq!(green.to_string(), source, "{source:?}");
        assert_eq!(token_count(&declaration(&green), SyntaxKind::CastKw), 1);
    }

    for source in [
        "casting(x): T;",
        "castaway(x): T;",
        "mycast(x): T;",
        "my castish(x): T;",
        "our\ncast(x): T;",
        "\ncast(x): T;",
    ] {
        let (green, exit, remainder) =
            run_cast_declaration(source, 0, 700, LineEntry::InLine, None);
        assert!(exit.is_none(), "{source:?}");
        assert_eq!(green.to_string(), "", "{source:?}");
        assert_eq!(remainder, source, "{source:?}");
    }

    let source = "my cast = value";
    let (green, exit, remainder) = run_cast_declaration(source, 0, 0, LineEntry::InLine, None);
    assert!(exit.is_some());
    assert_eq!(green.to_string(), source);
    assert_eq!(remainder, "");
    let declaration = declaration(&green);
    assert_eq!(count(&declaration, SyntaxKind::Missing), 1);
    assert_eq!(count(&declaration, SyntaxKind::BindingStatement), 0);
    assert_eq!(count(&declaration, SyntaxKind::CastBody), 1);

    let (green, _) = run_statement("cast(x): T;");
    assert_eq!(green.to_string(), "cast(x): T;");
    assert_eq!(
        SyntaxNode::new_root(green)
            .descendants()
            .filter(|node| node.kind() == SyntaxKind::CastDeclaration)
            .count(),
        1
    );
}

#[test]
fn cast_pattern_reuses_full_pattern_surface_and_nested_close_handoffs() {
    for source in [
        "cast(:symbol): T;",
        "cast(x: Source): Target;",
        "cast({x = 1}): T;",
        "cast([x, ..rest]): T;",
        "cast((x | y)): T;",
    ] {
        let (green, _, remainder) = run_cast_declaration(source, 0, 0, LineEntry::InLine, None);
        assert_eq!(green.to_string(), source, "{source:?}");
        assert_eq!(remainder, "", "{source:?}");
        let declaration = declaration(&green);
        assert_eq!(count(&declaration, SyntaxKind::Missing), 0, "{source:?}");
        assert_eq!(count(&declaration, SyntaxKind::Error), 0, "{source:?}");
    }

    for source in ["cast([x): B;", "cast({x): B;", "cast(x: '[A): B;"] {
        let (green, _, remainder) = run_cast_declaration(source, 0, 0, LineEntry::InLine, None);
        assert_eq!(green.to_string(), source, "{source:?}");
        assert_eq!(remainder, "", "{source:?}");
        let declaration = declaration(&green);
        assert_eq!(count(&declaration, SyntaxKind::Missing), 1, "{source:?}");
        assert_eq!(count(&declaration, SyntaxKind::Error), 0, "{source:?}");
        assert_eq!(
            token_count(&declaration, SyntaxKind::RParen),
            1,
            "{source:?}"
        );
    }

    let source = "cast((x @): B;";
    let (green, _, remainder) = run_cast_declaration(source, 0, 0, LineEntry::InLine, None);
    assert_eq!(green.to_string(), source);
    assert_eq!(remainder, "");
    let declaration = declaration(&green);
    assert_eq!(count(&declaration, SyntaxKind::Missing), 1);
    assert_eq!(count(&declaration, SyntaxKind::Error), 1);
    assert_eq!(token_count(&declaration, SyntaxKind::RParen), 1);
}

#[test]
fn cast_target_reuses_full_type_surface_with_nested_form_punctuation_suspended() {
    for source in [
        "cast(x): List(Int)::Result Arg -> Out -> Final;",
        "cast(x): F(:{A});",
        "cast(x): [e] F [io] -> U;",
        "cast(x): {field: A};",
    ] {
        let (green, _, remainder) = run_cast_declaration(source, 0, 0, LineEntry::InLine, None);
        assert_eq!(green.to_string(), source, "{source:?}");
        assert_eq!(remainder, "", "{source:?}");
        let declaration = declaration(&green);
        assert_eq!(count(&declaration, SyntaxKind::CastTarget), 1, "{source:?}");
        assert_eq!(count(&declaration, SyntaxKind::Missing), 0, "{source:?}");
        assert_eq!(count(&declaration, SyntaxKind::Error), 0, "{source:?}");
        assert_eq!(
            token_count(&declaration, SyntaxKind::Semicolon),
            1,
            "{source:?}"
        );
    }
}

#[test]
fn cast_pattern_prefix_and_close_recovery_is_bounded() {
    for (source, missing, errors) in [
        ("cast;", 1, 0),
        ("cast();", 2, 0),
        ("cast(@): B;", 0, 1),
        ("cast(x @ ): B;", 0, 1),
        ("cast @ (x): B;", 0, 1),
        ("cast @ : B;", 0, 1),
        ("cast @ = value", 0, 1),
    ] {
        let (green, _, remainder) = run_cast_declaration(source, 0, 0, LineEntry::InLine, None);
        assert_eq!(green.to_string(), source, "{source:?}");
        assert_eq!(remainder, "", "{source:?}");
        let declaration = declaration(&green);
        assert_eq!(
            count(&declaration, SyntaxKind::Missing),
            missing,
            "{source:?}"
        );
        assert_eq!(count(&declaration, SyntaxKind::Error), errors, "{source:?}");
    }

    let source = "cast x ) tail";
    let (green, exit, remainder) = run_cast_declaration(
        source,
        stops_for(TokenKind::RParen),
        0,
        LineEntry::InLine,
        None,
    );
    assert_eq!(green.to_string(), "cast x");
    assert_eq!(remainder, " tail");
    let declaration = declaration(&green);
    assert_eq!(count(&declaration, SyntaxKind::Missing), 1);
    assert_eq!(count(&declaration, SyntaxKind::Error), 0);
    assert_eq!(token_count(&declaration, SyntaxKind::RParen), 0);
    let mut pending = pending_item(exit);
    assert_eq!(pending.payload_view().token_kind(), Some(TokenKind::RParen));
    assert_eq!(emit_pending_leading_text(&mut pending), " ");
}

#[test]
fn cast_target_and_form_recovery_keep_starters_distinct() {
    for (source, missing, errors, targets, bodies) in [
        ("cast(x) B;", 1, 0, 1, 0),
        ("cast(x) @ : B;", 0, 1, 1, 0),
        ("cast(x);", 1, 0, 0, 0),
        ("cast(x): ;", 1, 0, 1, 0),
        ("cast(x): @ ;", 0, 1, 1, 0),
        ("cast(x): B", 1, 0, 1, 0),
        ("cast(x): B = value", 0, 0, 1, 1),
        ("cast(x): B == value", 0, 1, 1, 0),
    ] {
        let (green, _, remainder) = run_cast_declaration(source, 0, 0, LineEntry::InLine, None);
        assert_eq!(green.to_string(), source, "{source:?}");
        assert_eq!(remainder, "", "{source:?}");
        let declaration = declaration(&green);
        assert_eq!(
            count(&declaration, SyntaxKind::Missing),
            missing,
            "{source:?}"
        );
        assert_eq!(count(&declaration, SyntaxKind::Error), errors, "{source:?}");
        assert_eq!(
            count(&declaration, SyntaxKind::CastTarget),
            targets,
            "{source:?}"
        );
        assert_eq!(
            count(&declaration, SyntaxKind::CastBody),
            bodies,
            "{source:?}"
        );
    }
}

#[test]
fn cast_malformed_body_introducer_retries_actual_form_starters() {
    for (source, form, body) in [
        ("cast(x): A @ ;", SyntaxKind::Semicolon, 0),
        ("cast(x): A @ = value", SyntaxKind::Equals, 1),
    ] {
        let (green, _, remainder) = run_cast_declaration(source, 0, 0, LineEntry::InLine, None);
        assert_eq!(green.to_string(), source, "{source:?}");
        assert_eq!(remainder, "", "{source:?}");
        let declaration = declaration(&green);
        assert_eq!(count(&declaration, SyntaxKind::Error), 1, "{source:?}");
        assert_eq!(count(&declaration, SyntaxKind::Missing), 0, "{source:?}");
        assert_eq!(token_count(&declaration, form), 1, "{source:?}");
        assert_eq!(
            count(&declaration, SyntaxKind::CastBody),
            body,
            "{source:?}"
        );
        assert_eq!(
            declaration
                .descendants()
                .find(|node| node.kind() == SyntaxKind::Error)
                .expect("BodyIntroducer Error")
                .to_string(),
            "@",
            "{source:?}"
        );
    }
}

#[test]
fn cast_definition_body_preserves_boundaries_and_recovers_one_run() {
    for source in [
        "cast(x): T = value: argument",
        "cast(x): T = value with: body",
        "cast(x): T = value { field: x }",
        "cast(x): T =\r\n  my y = x\r\n  y",
    ] {
        let (green, _, remainder) = run_cast_declaration(source, 0, 0, LineEntry::InLine, None);
        assert_eq!(green.to_string(), source, "{source:?}");
        assert_eq!(remainder, "", "{source:?}");
        let declaration = declaration(&green);
        assert_eq!(count(&declaration, SyntaxKind::Missing), 0, "{source:?}");
        assert_eq!(count(&declaration, SyntaxKind::Error), 0, "{source:?}");
    }

    let source = "cast(x): T = @ value";
    let (green, _, remainder) = run_cast_declaration(source, 0, 0, LineEntry::InLine, None);
    assert_eq!(green.to_string(), source);
    assert_eq!(remainder, "");
    let node = declaration(&green);
    assert_eq!(count(&node, SyntaxKind::Error), 1);
    assert_eq!(count(&node, SyntaxKind::Missing), 0);
    let source = "cast(x): T = @   ";
    let (green, _, remainder) = run_cast_declaration(source, 0, 0, LineEntry::InLine, None);
    assert_eq!(green.to_string(), source);
    assert_eq!(remainder, "");
    let node = declaration(&green);
    assert_eq!(count(&node, SyntaxKind::Error), 1);
    assert_eq!(count(&node, SyntaxKind::Missing), 0);
    assert_eq!(
        node.descendants()
            .find(|descendant| descendant.kind() == SyntaxKind::Error)
            .expect("PatternIntroducer Error")
            .to_string(),
        "@   "
    );

    let source = "cast(x): T = ; tail";
    let (green, exit, remainder) = run_cast_declaration(source, 0, 0, LineEntry::InLine, None);
    assert_eq!(green.to_string(), "cast(x): T =");
    assert_eq!(remainder, " tail");
    assert_eq!(count(&declaration(&green), SyntaxKind::Missing), 1);
    let mut pending = pending_item(exit);
    assert_eq!(
        pending.payload_view().token_kind(),
        Some(TokenKind::Semicolon)
    );
    assert_eq!(emit_pending_leading_text(&mut pending), " ");

    let source = "cast(x): T =\ny";
    let (green, exit, remainder) = run_cast_declaration(source, 0, 0, LineEntry::InLine, None);
    assert_eq!(green.to_string(), "cast(x): T =");
    assert_eq!(remainder, "");
    assert_eq!(count(&declaration(&green), SyntaxKind::Missing), 1);
    let mut pending = pending_item(exit);
    assert_eq!(pending.payload_view().spelling(), Some("y"));
    assert_eq!(emit_pending_leading_text(&mut pending), "\n");
}

#[test]
fn cast_phase_transitions_preserve_disallowed_newline_gaps() {
    for (source, accepted, pending_kind, leading, missing, errors) in [
        ("cast(x)\n;", "cast(x)", TokenKind::Semicolon, "\n", 1, 0),
        (
            "cast(x)\r\n;",
            "cast(x)",
            TokenKind::Semicolon,
            "\r\n",
            1,
            0,
        ),
        ("cast(x\n: T;", "cast(x", TokenKind::Colon, "\n", 1, 0),
        (
            "cast(x):\r\n= value",
            "cast(x):",
            TokenKind::Equals,
            "\r\n",
            1,
            0,
        ),
        (
            "cast(x):\n= value",
            "cast(x):",
            TokenKind::Equals,
            "\n",
            1,
            0,
        ),
        ("cast(@\n;", "cast(@", TokenKind::Semicolon, "\n", 0, 1),
        (
            "cast(x @\r\n: T;",
            "cast(x @",
            TokenKind::Colon,
            "\r\n",
            0,
            1,
        ),
        (
            "cast(x) @\n;",
            "cast(x) @",
            TokenKind::Semicolon,
            "\n",
            0,
            1,
        ),
    ] {
        let (green, exit, _) = run_cast_declaration(source, 0, 0, LineEntry::InLine, None);
        assert_eq!(green.to_string(), accepted, "{source:?}");
        let declaration = declaration(&green);
        assert_eq!(
            count(&declaration, SyntaxKind::Missing),
            missing,
            "{source:?}"
        );
        assert_eq!(count(&declaration, SyntaxKind::Error), errors, "{source:?}");
        let mut pending = pending_item(exit);
        assert_eq!(pending.payload_view().token_kind(), Some(pending_kind));
        assert_eq!(
            emit_pending_leading_text(&mut pending),
            leading,
            "{source:?}"
        );
    }

    for (source, missing) in [
        ("cast(x)\n  ;", 1),
        ("cast(x)\r\n  : T;", 0),
        ("cast(x):\n  = value", 1),
    ] {
        let (green, _, remainder) = run_cast_declaration(source, 0, 0, LineEntry::InLine, None);
        assert_eq!(green.to_string(), source, "{source:?}");
        assert_eq!(remainder, "", "{source:?}");
        let declaration = declaration(&green);
        assert_eq!(
            count(&declaration, SyntaxKind::Missing),
            missing,
            "{source:?}"
        );
        assert_eq!(count(&declaration, SyntaxKind::Error), 0, "{source:?}");
    }
}

#[test]
fn cast_malformed_pattern_introducer_owns_only_same_line_eof_trivia() {
    let source = "cast @   ";
    let (green, exit, remainder) = run_cast_declaration(source, 0, 0, LineEntry::InLine, None);
    assert_eq!(green.to_string(), source);
    assert_eq!(remainder, "");
    let node = declaration(&green);
    assert_eq!(count(&node, SyntaxKind::Error), 1);
    assert_eq!(count(&node, SyntaxKind::Missing), 0);
    assert_eq!(
        node.descendants()
            .find(|descendant| descendant.kind() == SyntaxKind::Error)
            .expect("PatternIntroducer Error")
            .to_string(),
        "@   "
    );
    let mut pending = pending_item(exit);
    assert!(pending.payload_view().is_eof());
    assert_eq!(emit_pending_leading_text(&mut pending), "");

    for source in ["cast @\n", "cast @\r\n  "] {
        let (green, exit, remainder) = run_cast_declaration(source, 0, 0, LineEntry::InLine, None);
        assert_eq!(green.to_string(), "cast @", "{source:?}");
        assert_eq!(remainder, "", "{source:?}");
        let declaration = declaration(&green);
        assert_eq!(count(&declaration, SyntaxKind::Error), 1, "{source:?}");
        assert_eq!(count(&declaration, SyntaxKind::Missing), 0, "{source:?}");
        assert_eq!(
            declaration
                .descendants()
                .find(|descendant| descendant.kind() == SyntaxKind::Error)
                .expect("PatternIntroducer Error")
                .to_string(),
            "@",
            "{source:?}"
        );
        let mut pending = pending_item(exit);
        assert!(pending.payload_view().is_eof());
        assert_eq!(
            emit_pending_leading_text(&mut pending),
            &source["cast @".len()..],
            "{source:?}"
        );
    }
}

#[test]
fn cast_malformed_target_introducer_owns_only_same_line_eof_trivia() {
    let source = "cast(x) @   ";
    let (green, exit, remainder) = run_cast_declaration(source, 0, 0, LineEntry::InLine, None);
    assert_eq!(green.to_string(), source);
    assert_eq!(remainder, "");
    let node = declaration(&green);
    assert_eq!(count(&node, SyntaxKind::Error), 1);
    assert_eq!(count(&node, SyntaxKind::Missing), 0);
    assert_eq!(
        node.descendants()
            .find(|descendant| descendant.kind() == SyntaxKind::Error)
            .expect("TargetIntroducer Error")
            .to_string(),
        "@   "
    );
    let mut pending = pending_item(exit);
    assert!(pending.payload_view().is_eof());
    assert_eq!(emit_pending_leading_text(&mut pending), "");

    for source in ["cast(x) @\n", "cast(x) @\r\n  "] {
        let (green, exit, remainder) = run_cast_declaration(source, 0, 0, LineEntry::InLine, None);
        assert_eq!(green.to_string(), "cast(x) @", "{source:?}");
        assert_eq!(remainder, "", "{source:?}");
        let declaration = declaration(&green);
        assert_eq!(count(&declaration, SyntaxKind::Error), 1, "{source:?}");
        assert_eq!(count(&declaration, SyntaxKind::Missing), 0, "{source:?}");
        assert_eq!(
            declaration
                .descendants()
                .find(|descendant| descendant.kind() == SyntaxKind::Error)
                .expect("TargetIntroducer Error")
                .to_string(),
            "@",
            "{source:?}"
        );
        let mut pending = pending_item(exit);
        assert!(pending.payload_view().is_eof());
        assert_eq!(
            emit_pending_leading_text(&mut pending),
            &source["cast(x) @".len()..],
            "{source:?}"
        );
    }
}

#[test]
fn cast_malformed_body_introducer_owns_only_same_line_eof_trivia() {
    let source = "cast(x): A @   ";
    let (green, exit, remainder) = run_cast_declaration(source, 0, 0, LineEntry::InLine, None);
    assert_eq!(green.to_string(), source);
    assert_eq!(remainder, "");
    let node = declaration(&green);
    assert_eq!(count(&node, SyntaxKind::Error), 1);
    assert_eq!(count(&node, SyntaxKind::Missing), 0);
    assert_eq!(
        node.descendants()
            .find(|descendant| descendant.kind() == SyntaxKind::Error)
            .expect("BodyIntroducer Error")
            .to_string(),
        "@   "
    );
    let mut pending = pending_item(exit);
    assert!(pending.payload_view().is_eof());
    assert_eq!(emit_pending_leading_text(&mut pending), "");

    for source in ["cast(x): A @\n", "cast(x): A @\r\n  "] {
        let (green, exit, remainder) = run_cast_declaration(source, 0, 0, LineEntry::InLine, None);
        assert_eq!(green.to_string(), "cast(x): A @", "{source:?}");
        assert_eq!(remainder, "", "{source:?}");
        let declaration = declaration(&green);
        assert_eq!(count(&declaration, SyntaxKind::Error), 1, "{source:?}");
        assert_eq!(count(&declaration, SyntaxKind::Missing), 0, "{source:?}");
        assert_eq!(
            declaration
                .descendants()
                .find(|descendant| descendant.kind() == SyntaxKind::Error)
                .expect("BodyIntroducer Error")
                .to_string(),
            "@",
            "{source:?}"
        );
        let mut pending = pending_item(exit);
        assert!(pending.payload_view().is_eof());
        assert_eq!(
            emit_pending_leading_text(&mut pending),
            &source["cast(x): A @".len()..],
            "{source:?}"
        );
    }
}

#[test]
fn cast_malformed_body_owns_only_same_line_eof_trivia() {
    let source = "cast(x): A = @   ";
    let (green, exit, remainder) = run_cast_declaration(source, 0, 0, LineEntry::InLine, None);
    assert_eq!(green.to_string(), source);
    assert_eq!(remainder, "");
    let node = declaration(&green);
    assert_eq!(count(&node, SyntaxKind::Error), 1);
    assert_eq!(count(&node, SyntaxKind::Missing), 0);
    assert_eq!(
        node.descendants()
            .find(|descendant| descendant.kind() == SyntaxKind::Error)
            .expect("Body Error")
            .to_string(),
        "@   "
    );
    let mut pending = pending_item(exit);
    assert!(pending.payload_view().is_eof());
    assert_eq!(emit_pending_leading_text(&mut pending), "");

    for source in ["cast(x): A = @\n", "cast(x): A = @\r\n  "] {
        let (green, exit, remainder) = run_cast_declaration(source, 0, 0, LineEntry::InLine, None);
        assert_eq!(green.to_string(), "cast(x): A = @", "{source:?}");
        assert_eq!(remainder, "", "{source:?}");
        let declaration = declaration(&green);
        assert_eq!(count(&declaration, SyntaxKind::Error), 1, "{source:?}");
        assert_eq!(count(&declaration, SyntaxKind::Missing), 0, "{source:?}");
        assert_eq!(
            declaration
                .descendants()
                .find(|descendant| descendant.kind() == SyntaxKind::Error)
                .expect("Body Error")
                .to_string(),
            "@",
            "{source:?}"
        );
        let mut pending = pending_item(exit);
        assert!(pending.payload_view().is_eof());
        assert_eq!(
            emit_pending_leading_text(&mut pending),
            &source["cast(x): A = @".len()..],
            "{source:?}"
        );
    }
}

#[test]
fn cast_indented_body_recovery_keeps_the_child_role() {
    let source = "cast(x): A =\n  ";
    let (_, _, records, remainder) = typed_cast(source, 0, None, 0, None);
    assert_eq!(remainder, "");
    assert!(records.iter().any(|record| {
        record.site.role
            == crate::recovery_record::GrammarRole::Declaration(
                crate::recovery_record::DeclarationRole::Cast(CastRole::IndentedStatement),
            )
    }));
    assert!(!records.iter().any(|record| {
        record.site.role
            == crate::recovery_record::GrammarRole::Declaration(
                crate::recovery_record::DeclarationRole::Cast(CastRole::Body),
            )
    }));
}

#[test]
fn cast_local_and_ambient_close_authority_preserves_exact_items() {
    let source = "cast([x ) ) tail";
    let (green, exit, remainder) = run_cast_declaration(
        source,
        stops_for(TokenKind::RParen),
        0,
        LineEntry::InLine,
        None,
    );
    assert_eq!(green.to_string(), "cast([x )");
    assert_eq!(remainder, " tail");
    let node = declaration(&green);
    assert_eq!(count(&node, SyntaxKind::Missing), 2);
    assert_eq!(token_count(&node, SyntaxKind::RParen), 1);
    let mut pending = pending_item(exit);
    assert_eq!(pending.payload_view().token_kind(), Some(TokenKind::RParen));
    assert_eq!(emit_pending_leading_text(&mut pending), " ");

    let source = "cast([x } tail";
    let (green, exit, remainder) = run_cast_declaration(
        source,
        stops_for(TokenKind::RBrace),
        0,
        LineEntry::InLine,
        None,
    );
    assert_eq!(green.to_string(), "cast([x");
    assert_eq!(remainder, " tail");
    assert_eq!(count(&declaration(&green), SyntaxKind::Missing), 1);
    let mut pending = pending_item(exit);
    assert_eq!(pending.payload_view().token_kind(), Some(TokenKind::RBrace));
    assert_eq!(emit_pending_leading_text(&mut pending), " ");

    let source = "cast(x): T else tail";
    let (green, exit, remainder) =
        run_cast_declaration(source, STOP_ELSE, 0, LineEntry::InLine, None);
    assert_eq!(green.to_string(), "cast(x): T");
    assert_eq!(remainder, " tail");
    assert_eq!(count(&declaration(&green), SyntaxKind::Missing), 1);
    let mut pending = pending_item(exit);
    assert_eq!(pending.payload_view().spelling(), Some("else"));
    assert_eq!(emit_pending_leading_text(&mut pending), " ");
}

#[test]
fn cast_fence_and_origin_boundary_remain_outer_owned() {
    use crate::lexical::item::{BorrowedTarget, Boundary};
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
    let origin = 12_000;
    let accepted = "> > cast(x): T";
    let source = format!("{accepted}\r\n> > ```\r\nouter");
    let (green, exit, remainder) =
        run_cast_declaration(&source, 0, origin, LineEntry::PhysicalStart, Some(&fence));
    assert_eq!(green.to_string(), accepted);
    assert_eq!(remainder, "> > ```\r\nouter");
    assert_eq!(count(&declaration(&green), SyntaxKind::Missing), 1);
    let boundary = pending_item(exit);
    let (leading, pending) = emit_terminal_leading_text(boundary);
    assert_eq!(leading, "\r\n");
    assert_eq!(pending.coordinate(), origin + accepted.len() + 2);
    assert!(matches!(
        pending.into_kind(),
        Boundary::BorrowedClose(BorrowedTarget::YumarkFence(_))
    ));

    let (_, _, records, typed_remainder) = typed_cast_at(
        &source,
        origin,
        None,
        0,
        LineEntry::PhysicalStart,
        Some(&fence),
    );
    assert_eq!(typed_remainder, "> > ```\r\nouter");
    assert_eq!(
        records,
        [cast_body_introducer_record(
            0,
            RecoveryKind::Missing,
            origin + accepted.len() + 2..origin + accepted.len() + 2,
        )]
    );

    let accepted = "> > cast(x): A =";
    let source = format!("{accepted}\r\n> > ```\r\nouter");
    let (_, _, records, typed_remainder) = typed_cast_at(
        &source,
        origin,
        None,
        0,
        LineEntry::PhysicalStart,
        Some(&fence),
    );
    assert_eq!(typed_remainder, "> > ```\r\nouter");
    assert_eq!(
        records,
        [cast_body_record(
            0,
            RecoveryKind::Missing,
            origin + accepted.len() + 2..origin + accepted.len() + 2,
        )]
    );

    let accepted = "> > cast @";
    let source = format!("{accepted}\r\n> > ```\r\nouter");
    let (green, exit, remainder) =
        run_cast_declaration(&source, 0, origin, LineEntry::PhysicalStart, Some(&fence));
    assert_eq!(green.to_string(), accepted);
    assert_eq!(remainder, "> > ```\r\nouter");
    let declaration = declaration(&green);
    assert_eq!(count(&declaration, SyntaxKind::Error), 1);
    assert_eq!(count(&declaration, SyntaxKind::Missing), 0);
    let boundary = pending_item(exit);
    let (leading, pending) = emit_terminal_leading_text(boundary);
    assert_eq!(leading, "\r\n");
    assert!(matches!(
        pending.into_kind(),
        Boundary::BorrowedClose(BorrowedTarget::YumarkFence(_))
    ));

    let (_, _, records, typed_remainder) = typed_cast_at(
        &source,
        origin,
        None,
        0,
        LineEntry::PhysicalStart,
        Some(&fence),
    );
    assert_eq!(typed_remainder, "> > ```\r\nouter");
    assert_eq!(
        records,
        [pattern_introducer_record(
            0,
            RecoveryKind::Error,
            origin + "> > cast ".len()..origin + accepted.len(),
        )]
    );

    let accepted = "> > cast(";
    let source = format!("{accepted}\r\n> > ```\r\nouter");
    let (_, _, records, typed_remainder) = typed_cast_at(
        &source,
        origin,
        None,
        0,
        LineEntry::PhysicalStart,
        Some(&fence),
    );
    assert_eq!(typed_remainder, "> > ```\r\nouter");
    assert_eq!(
        records,
        [cast_pattern_record(0, origin + accepted.len() + 2)]
    );

    let accepted = "> > cast(x) @";
    let source = format!("{accepted}\r\n> > ```\r\nouter");
    let (_, _, records, typed_remainder) = typed_cast_at(
        &source,
        origin,
        None,
        0,
        LineEntry::PhysicalStart,
        Some(&fence),
    );
    assert_eq!(typed_remainder, "> > ```\r\nouter");
    assert_eq!(
        records,
        [cast_target_introducer_record(
            0,
            RecoveryKind::Error,
            origin + "> > cast(x) ".len()..origin + accepted.len(),
        )]
    );

    let accepted = "> > cast(x): A @";
    let source = format!("{accepted}\r\n> > ```\r\nouter");
    let (_, _, records, typed_remainder) = typed_cast_at(
        &source,
        origin,
        None,
        0,
        LineEntry::PhysicalStart,
        Some(&fence),
    );
    assert_eq!(typed_remainder, "> > ```\r\nouter");
    assert_eq!(
        records,
        [cast_body_introducer_record(
            0,
            RecoveryKind::Error,
            origin + "> > cast(x): A ".len()..origin + accepted.len(),
        )]
    );
}
