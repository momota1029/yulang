use crate::tests::support::*;
use crate::{
    ambient_claim::AmbientClaimView,
    handoff::MlMode,
    recovery_record::{
        ConstructRole, Delimiter, DiagnosticId, ExpectationSources, ExpectedSyntax, ExpressionRole,
        GrammarRole, PunctuationEvidence, RecoveryKind, RecoverySiteKey, SyntaxExpectation,
        UnexpectedCategory, UnexpectedSyntax,
    },
    statement::StatementLineHandoff,
};
use std::{ops::Range, sync::Arc};

#[derive(Clone, Copy)]
enum Form {
    Group,
    Call,
    Index,
    Tuple,
    Record,
}

impl Form {
    fn item(self) -> ExpressionRole {
        match self {
            Self::Group => ExpressionRole::Nud,
            Self::Call => ExpressionRole::CallArgument,
            Self::Index => ExpressionRole::IndexItem,
            Self::Tuple => ExpressionRole::ProjectionTupleItem,
            Self::Record => ExpressionRole::ProjectionRecordItem,
        }
    }
    fn separator(self) -> ExpressionRole {
        match self {
            Self::Group => ExpressionRole::ParenthesizedSeparator,
            Self::Call => ExpressionRole::CallArgumentSeparator,
            Self::Index => ExpressionRole::IndexSeparator,
            Self::Tuple => ExpressionRole::ProjectionTupleSeparator,
            Self::Record => ExpressionRole::ProjectionRecordSeparator,
        }
    }
    fn closing(self) -> GrammarRole {
        GrammarRole::ClosingDelimiter {
            owner: match self {
                Self::Group => ConstructRole::ExpressionGroup,
                Self::Call => ConstructRole::ArgumentList,
                Self::Index => ConstructRole::IndexTail,
                Self::Tuple => ConstructRole::ProjectionTupleTail,
                Self::Record => ConstructRole::ProjectionRecordTail,
            },
            delimiter: match self {
                Self::Index => Delimiter::Bracket,
                Self::Record => Delimiter::Brace,
                _ => Delimiter::Parenthesis,
            },
        }
    }
}

fn parse<'s>(
    source: &'s str,
    form: Form,
    origin: usize,
    fence: Option<&FenceBoundary>,
    frozen: Option<&[CommittedRecoveryRecord]>,
) -> (
    GreenNode,
    NormalizedExit,
    &'s str,
    Vec<CommittedRecoveryRecord>,
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
    let exit = crate::expression::delimited::delimited_items_normalized(
        crate::cursor::SyntaxIn::new(&mut input, &mut recover, &mut output),
        match form {
            Form::Group => crate::expression::delimited::DelimitedOwner::Parenthesized,
            Form::Call => crate::expression::delimited::DelimitedOwner::Call,
            Form::Index => crate::expression::delimited::DelimitedOwner::Index,
            Form::Tuple => crate::expression::delimited::DelimitedOwner::ProjectionTuple,
            Form::Record => crate::expression::delimited::DelimitedOwner::ProjectionRecord,
        },
        0,
        0,
        if matches!(form, Form::Group) {
            MlMode::LayoutOnly
        } else {
            MlMode::All
        },
        StatementLineHandoff::OrdinaryLayout,
        origin,
        LineEntry::InLine,
        fence,
        Some(AmbientClaimView::root_statement(0)).into(),
    );
    output.finish_node();
    let (green, records) = (output.finish(), recover.finish_recoveries_for_test());
    (green, exit, input, records)
}

fn record(
    role: GrammarRole,
    kind: RecoveryKind,
    range: Range<usize>,
    category: UnexpectedCategory,
) -> CommittedRecoveryRecord {
    let expected = match role {
        GrammarRole::ClosingDelimiter { delimiter, .. } => {
            ExpectedSyntax::Punctuation(PunctuationEvidence::Close(delimiter))
        }
        GrammarRole::Expression(
            ExpressionRole::ParenthesizedSeparator
            | ExpressionRole::CallArgumentSeparator
            | ExpressionRole::IndexSeparator
            | ExpressionRole::ProjectionTupleSeparator
            | ExpressionRole::ProjectionRecordSeparator,
        ) => ExpectedSyntax::DelimitedSequenceSeparator,
        _ => ExpectedSyntax::Expression,
    };
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
                category,
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

fn check(source: &str, form: Form, mut expected: Vec<CommittedRecoveryRecord>) {
    for (index, record) in expected.iter_mut().enumerate() {
        record.id = DiagnosticId(index as u32);
    }
    let (green, _, remainder, actual) = parse(source, form, 0, None, None);
    assert_eq!(actual, expected, "{source:?}");
    assert_eq!(green.to_string(), source);
    assert_eq!(remainder, "");
    let (reconciled, _, remainder, records) = parse(source, form, 0, None, Some(&actual));
    assert_eq!(reconciled, green);
    assert_eq!(records, actual);
    assert_eq!(remainder, "");
}

#[test]
fn all_descriptors_publish_item_separator_and_close_records() {
    for (form, close) in [
        (Form::Group, ')'),
        (Form::Call, ')'),
        (Form::Index, ']'),
        (Form::Tuple, ')'),
        (Form::Record, '}'),
    ] {
        let item = GrammarRole::Expression(form.item());
        let missing = |range| {
            record(
                item,
                RecoveryKind::Missing,
                range,
                UnexpectedCategory::OtherCharacter,
            )
        };
        let error = |range| {
            record(
                item,
                RecoveryKind::Error,
                range,
                UnexpectedCategory::OtherCharacter,
            )
        };
        check(&format!("{close}"), form, vec![]);
        check(&format!("x,y{close}"), form, vec![]);
        if !matches!(form, Form::Group) {
            check(&format!("x;y{close}"), form, vec![]);
        }
        check(
            &format!("1x{close}"),
            form,
            vec![record(
                GrammarRole::Expression(form.separator()),
                RecoveryKind::Missing,
                1..1,
                UnexpectedCategory::OtherCharacter,
            )],
        );
        check(
            &format!(",,{close}"),
            form,
            vec![missing(0..0), missing(1..1)],
        );
        check(&format!("@ x{close}"), form, vec![error(0..1)]);
        check(&format!("@,{close}"), form, vec![error(0..1)]);
        check(&format!("@{close}"), form, vec![error(0..1)]);
        check(
            " ",
            form,
            vec![record(
                form.closing(),
                RecoveryKind::Missing,
                1..1,
                UnexpectedCategory::OtherCharacter,
            )],
        );
        check(
            "@",
            form,
            vec![
                error(0..1),
                record(
                    form.closing(),
                    RecoveryKind::Missing,
                    1..1,
                    UnexpectedCategory::OtherCharacter,
                ),
            ],
        );
        check(
            "",
            form,
            vec![record(
                form.closing(),
                RecoveryKind::Missing,
                0..0,
                UnexpectedCategory::OtherCharacter,
            )],
        );
        check(
            &format!("x @ y{close}"),
            form,
            vec![record(
                GrammarRole::Expression(form.separator()),
                RecoveryKind::Error,
                2..3,
                UnexpectedCategory::OtherCharacter,
            )],
        );
        let wrong = if close == ']' { ')' } else { ']' };
        let delimiter = if wrong == ')' {
            Delimiter::Parenthesis
        } else {
            Delimiter::Bracket
        };
        check(
            &format!(" {wrong}{close}"),
            form,
            vec![record(
                form.closing(),
                RecoveryKind::Error,
                0..2,
                UnexpectedCategory::Punctuation(PunctuationEvidence::Close(delimiter)),
            )],
        );
    }
}

#[test]
fn parenthesized_semicolon_is_a_separator_error_in_every_phase() {
    let error = |range| {
        record(
            GrammarRole::Expression(ExpressionRole::ParenthesizedSeparator),
            RecoveryKind::Error,
            range,
            UnexpectedCategory::Punctuation(PunctuationEvidence::Semicolon),
        )
    };
    check(";x)", Form::Group, vec![error(0..1)]);
    check(";;)", Form::Group, vec![error(0..1), error(1..2)]);
    check("x;)", Form::Group, vec![error(1..2)]);
    check(
        "x y)",
        Form::Group,
        vec![record(
            GrammarRole::Expression(ExpressionRole::ParenthesizedSeparator),
            RecoveryKind::Missing,
            1..1,
            UnexpectedCategory::OtherCharacter,
        )],
    );
}

#[test]
fn record_spread_rhs_is_typed_without_duplicate_missing() {
    let role = GrammarRole::Expression(ExpressionRole::ProjectionRecordSpreadRhs);
    check(
        "..,}",
        Form::Record,
        vec![record(
            role,
            RecoveryKind::Missing,
            2..2,
            UnexpectedCategory::OtherCharacter,
        )],
    );
    check(
        "..@ x}",
        Form::Record,
        vec![record(
            role,
            RecoveryKind::Error,
            2..3,
            UnexpectedCategory::OtherCharacter,
        )],
    );
    check(
        "..@,}",
        Form::Record,
        vec![record(
            role,
            RecoveryKind::Error,
            2..3,
            UnexpectedCategory::OtherCharacter,
        )],
    );
}

#[test]
fn lexical_errors_end_at_lf_and_crlf_implicit_separators() {
    for newline in ["\n", "\r\n"] {
        let source = format!("@{newline}@)");
        let role = GrammarRole::Expression(ExpressionRole::Nud);
        check(
            &source,
            Form::Group,
            vec![
                record(
                    role,
                    RecoveryKind::Error,
                    0..1,
                    UnexpectedCategory::OtherCharacter,
                ),
                record(
                    role,
                    RecoveryKind::Error,
                    1 + newline.len()..2 + newline.len(),
                    UnexpectedCategory::OtherCharacter,
                ),
            ],
        );
    }
}

#[test]
fn delimited_fence_and_nonzero_utf8_extents_reconcile() {
    use crate::lexical::yumark::{FenceOpener, FencePrefixPolicy};
    let fence = FenceBoundary {
        opener: FenceOpener {
            line: 0,
            marker: 0..3,
            marker_width: 3,
        },
        prefix_policy: FencePrefixPolicy::None,
        close_column: 0,
    };
    for form in [
        Form::Group,
        Form::Call,
        Form::Index,
        Form::Tuple,
        Form::Record,
    ] {
        let source = "é\r\n```\nouter";
        let (green, exit, remainder, records) = parse(source, form, 100, Some(&fence), None);
        assert_eq!(
            records,
            [record(
                form.closing(),
                RecoveryKind::Missing,
                104..104,
                UnexpectedCategory::OtherCharacter
            )]
        );
        assert_eq!(green.to_string(), "é");
        assert_eq!(remainder, "```\nouter");
        assert!(matches!(
            exit,
            NormalizedExit::Complete(Err(Either::Left(_)), LineEntry::PhysicalStart)
        ));
        let (again, _, _, frozen) = parse(source, form, 100, Some(&fence), Some(&records));
        assert_eq!(again, green);
        assert_eq!(frozen, records);
    }
}

fn full(
    source: &str,
    frozen: Option<&[CommittedRecoveryRecord]>,
) -> (GreenNode, Vec<CommittedRecoveryRecord>) {
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
        0,
        MlMode::All,
        StatementLineHandoff::OrdinaryLayout,
        0,
        LineEntry::InLine,
        None,
        Some(AmbientClaimView::root_statement(0)).into(),
        None,
    );
    assert!(exit.is_some());
    output.finish_node();
    (output.finish(), recover.finish_recoveries_for_test())
}

#[test]
fn parenthesized_collision_literals_keep_distinct_records_and_one_raw_topology() {
    for (source, expected) in [
        (
            "(@)",
            record(
                GrammarRole::Expression(ExpressionRole::Nud),
                RecoveryKind::Error,
                1..2,
                UnexpectedCategory::OtherCharacter,
            ),
        ),
        (
            "(;)",
            record(
                GrammarRole::Expression(ExpressionRole::ParenthesizedSeparator),
                RecoveryKind::Error,
                1..2,
                UnexpectedCategory::Punctuation(PunctuationEvidence::Semicolon),
            ),
        ),
        (
            "(])",
            record(
                GrammarRole::ClosingDelimiter {
                    owner: ConstructRole::ExpressionGroup,
                    delimiter: Delimiter::Parenthesis,
                },
                RecoveryKind::Error,
                1..2,
                UnexpectedCategory::Punctuation(PunctuationEvidence::Close(Delimiter::Bracket)),
            ),
        ),
    ] {
        let (green, records) = full(source, None);
        assert_eq!(records, [expected], "{source:?}");
        assert_eq!(green.to_string(), source, "{source:?}");

        let root = SyntaxNode::new_root(green.clone());
        let group = root
            .descendants()
            .find(|node| node.kind() == SyntaxKind::ParenthesizedExpression)
            .expect("parenthesized expression");
        assert_eq!(
            group
                .children_with_tokens()
                .map(|element| {
                    (
                        element.kind(),
                        usize::from(element.text_range().start())
                            ..usize::from(element.text_range().end()),
                    )
                })
                .collect::<Vec<_>>(),
            [
                (SyntaxKind::LParen, 0..1),
                (SyntaxKind::Error, 1..2),
                (SyntaxKind::RParen, 2..3),
            ],
            "{source:?}"
        );
        let middle = group.children_with_tokens().nth(1).unwrap();
        let error = middle
            .as_token()
            .expect("the raw collision leaf must remain an Error token");
        assert_eq!(error.kind(), SyntaxKind::Error, "{source:?}");
        assert_eq!(
            error.text_range(),
            rowan::TextRange::new(1.into(), 2.into())
        );
        assert!(
            !group
                .descendants_with_tokens()
                .any(|element| matches!(element.kind(), SyntaxKind::Missing | SyntaxKind::Invalid)),
            "{source:?}"
        );

        let (frozen, frozen_records) = full(source, Some(&records));
        assert_eq!(frozen, green, "{source:?}");
        assert_eq!(frozen_records, records, "{source:?}");
    }
}

#[test]
fn expression_delimited_raw_item_separator_and_foreign_close_matrix() {
    for (form, owner, source, role, range, category, direct) in [
        (
            Form::Group,
            SyntaxKind::ParenthesizedExpression,
            "(@)",
            GrammarRole::Expression(ExpressionRole::Nud),
            1..2,
            UnexpectedCategory::OtherCharacter,
            vec![
                (SyntaxKind::LParen, 0..1),
                (SyntaxKind::Error, 1..2),
                (SyntaxKind::RParen, 2..3),
            ],
        ),
        (
            Form::Group,
            SyntaxKind::ParenthesizedExpression,
            "(a @ b)",
            GrammarRole::Expression(ExpressionRole::ParenthesizedSeparator),
            3..4,
            UnexpectedCategory::OtherCharacter,
            vec![
                (SyntaxKind::LParen, 0..1),
                (SyntaxKind::OperatorChain, 1..2),
                (SyntaxKind::Whitespace, 2..3),
                (SyntaxKind::Error, 3..4),
                (SyntaxKind::OperatorChain, 4..6),
                (SyntaxKind::RParen, 6..7),
            ],
        ),
        (
            Form::Group,
            SyntaxKind::ParenthesizedExpression,
            "(])",
            Form::Group.closing(),
            1..2,
            UnexpectedCategory::Punctuation(PunctuationEvidence::Close(Delimiter::Bracket)),
            vec![
                (SyntaxKind::LParen, 0..1),
                (SyntaxKind::Error, 1..2),
                (SyntaxKind::RParen, 2..3),
            ],
        ),
        (
            Form::Call,
            SyntaxKind::CallTail,
            "f(@)",
            GrammarRole::Expression(ExpressionRole::CallArgument),
            2..3,
            UnexpectedCategory::OtherCharacter,
            vec![
                (SyntaxKind::LParen, 1..2),
                (SyntaxKind::Error, 2..3),
                (SyntaxKind::RParen, 3..4),
            ],
        ),
        (
            Form::Call,
            SyntaxKind::CallTail,
            "f(a @ b)",
            GrammarRole::Expression(ExpressionRole::CallArgumentSeparator),
            4..5,
            UnexpectedCategory::OtherCharacter,
            vec![
                (SyntaxKind::LParen, 1..2),
                (SyntaxKind::OperatorChain, 2..3),
                (SyntaxKind::Whitespace, 3..4),
                (SyntaxKind::Error, 4..5),
                (SyntaxKind::OperatorChain, 5..7),
                (SyntaxKind::RParen, 7..8),
            ],
        ),
        (
            Form::Call,
            SyntaxKind::CallTail,
            "f(])",
            Form::Call.closing(),
            2..3,
            UnexpectedCategory::Punctuation(PunctuationEvidence::Close(Delimiter::Bracket)),
            vec![
                (SyntaxKind::LParen, 1..2),
                (SyntaxKind::Error, 2..3),
                (SyntaxKind::RParen, 3..4),
            ],
        ),
        (
            Form::Index,
            SyntaxKind::IndexTail,
            "x[@]",
            GrammarRole::Expression(ExpressionRole::IndexItem),
            2..3,
            UnexpectedCategory::OtherCharacter,
            vec![
                (SyntaxKind::LBracket, 1..2),
                (SyntaxKind::Error, 2..3),
                (SyntaxKind::RBracket, 3..4),
            ],
        ),
        (
            Form::Index,
            SyntaxKind::IndexTail,
            "x[a @ b]",
            GrammarRole::Expression(ExpressionRole::IndexSeparator),
            4..5,
            UnexpectedCategory::OtherCharacter,
            vec![
                (SyntaxKind::LBracket, 1..2),
                (SyntaxKind::IndexItem, 2..3),
                (SyntaxKind::Whitespace, 3..4),
                (SyntaxKind::Error, 4..5),
                (SyntaxKind::IndexItem, 5..7),
                (SyntaxKind::RBracket, 7..8),
            ],
        ),
        (
            Form::Index,
            SyntaxKind::IndexTail,
            "x[)]",
            Form::Index.closing(),
            2..3,
            UnexpectedCategory::Punctuation(PunctuationEvidence::Close(Delimiter::Parenthesis)),
            vec![
                (SyntaxKind::LBracket, 1..2),
                (SyntaxKind::Error, 2..3),
                (SyntaxKind::RBracket, 3..4),
            ],
        ),
        (
            Form::Tuple,
            SyntaxKind::ProjectionTupleTail,
            "x.(@)",
            GrammarRole::Expression(ExpressionRole::ProjectionTupleItem),
            3..4,
            UnexpectedCategory::OtherCharacter,
            vec![
                (SyntaxKind::Dot, 1..2),
                (SyntaxKind::LParen, 2..3),
                (SyntaxKind::Error, 3..4),
                (SyntaxKind::RParen, 4..5),
            ],
        ),
        (
            Form::Tuple,
            SyntaxKind::ProjectionTupleTail,
            "x.(a @ b)",
            GrammarRole::Expression(ExpressionRole::ProjectionTupleSeparator),
            5..6,
            UnexpectedCategory::OtherCharacter,
            vec![
                (SyntaxKind::Dot, 1..2),
                (SyntaxKind::LParen, 2..3),
                (SyntaxKind::OperatorChain, 3..4),
                (SyntaxKind::Whitespace, 4..5),
                (SyntaxKind::Error, 5..6),
                (SyntaxKind::OperatorChain, 6..8),
                (SyntaxKind::RParen, 8..9),
            ],
        ),
        (
            Form::Tuple,
            SyntaxKind::ProjectionTupleTail,
            "x.(])",
            Form::Tuple.closing(),
            3..4,
            UnexpectedCategory::Punctuation(PunctuationEvidence::Close(Delimiter::Bracket)),
            vec![
                (SyntaxKind::Dot, 1..2),
                (SyntaxKind::LParen, 2..3),
                (SyntaxKind::Error, 3..4),
                (SyntaxKind::RParen, 4..5),
            ],
        ),
        (
            Form::Record,
            SyntaxKind::ProjectionRecordTail,
            "x.{@}",
            GrammarRole::Expression(ExpressionRole::ProjectionRecordItem),
            3..4,
            UnexpectedCategory::OtherCharacter,
            vec![
                (SyntaxKind::Dot, 1..2),
                (SyntaxKind::LBrace, 2..3),
                (SyntaxKind::Error, 3..4),
                (SyntaxKind::RBrace, 4..5),
            ],
        ),
        (
            Form::Record,
            SyntaxKind::ProjectionRecordTail,
            "x.{a @ b}",
            GrammarRole::Expression(ExpressionRole::ProjectionRecordSeparator),
            5..6,
            UnexpectedCategory::OtherCharacter,
            vec![
                (SyntaxKind::Dot, 1..2),
                (SyntaxKind::LBrace, 2..3),
                (SyntaxKind::OperatorChain, 3..4),
                (SyntaxKind::Whitespace, 4..5),
                (SyntaxKind::Error, 5..6),
                (SyntaxKind::OperatorChain, 6..8),
                (SyntaxKind::RBrace, 8..9),
            ],
        ),
        (
            Form::Record,
            SyntaxKind::ProjectionRecordTail,
            "x.{)}",
            Form::Record.closing(),
            3..4,
            UnexpectedCategory::Punctuation(PunctuationEvidence::Close(Delimiter::Parenthesis)),
            vec![
                (SyntaxKind::Dot, 1..2),
                (SyntaxKind::LBrace, 2..3),
                (SyntaxKind::Error, 3..4),
                (SyntaxKind::RBrace, 4..5),
            ],
        ),
    ] {
        let separator = matches!(
            role,
            GrammarRole::Expression(
                ExpressionRole::ParenthesizedSeparator
                    | ExpressionRole::CallArgumentSeparator
                    | ExpressionRole::IndexSeparator
                    | ExpressionRole::ProjectionTupleSeparator
                    | ExpressionRole::ProjectionRecordSeparator
            )
        );
        let expected = record(role, RecoveryKind::Error, range.clone(), category);
        let (green, records) = full(source, None);
        assert_eq!(records, [expected], "{source:?}");
        assert_eq!(green.to_string(), source, "{source:?}");

        let root = SyntaxNode::new_root(green.clone());
        let owner_node = root
            .descendants()
            .find(|node| node.kind() == owner)
            .expect("expression-delimited owner");
        assert_eq!(
            owner_node
                .children_with_tokens()
                .map(|element| {
                    (
                        element.kind(),
                        usize::from(element.text_range().start())
                            ..usize::from(element.text_range().end()),
                    )
                })
                .collect::<Vec<_>>(),
            direct,
            "{source:?}"
        );
        assert!(
            !owner_node
                .descendants_with_tokens()
                .any(|element| matches!(element.kind(), SyntaxKind::Missing | SyntaxKind::Invalid)),
            "{source:?}"
        );
        let error = owner_node
            .children_with_tokens()
            .find(|element| element.kind() == SyntaxKind::Error)
            .expect("owner-local raw Error");
        let error = error
            .as_token()
            .expect("owner-local raw Error must be a token");
        assert_eq!(
            error.text_range(),
            rowan::TextRange::new((range.start as u32).into(), (range.end as u32).into()),
            "{source:?}"
        );
        let admitted = owner_node
            .children()
            .filter(|node| {
                matches!(
                    node.kind(),
                    SyntaxKind::IndexItem | SyntaxKind::OperatorChain
                )
            })
            .collect::<Vec<_>>();
        if separator {
            assert_eq!(admitted.len(), 2, "{source:?}");
            assert!(
                admitted.iter().all(|node| node.kind()
                    == if matches!(form, Form::Index) {
                        SyntaxKind::IndexItem
                    } else {
                        SyntaxKind::OperatorChain
                    }),
                "{source:?}"
            );
        } else {
            assert!(admitted.is_empty(), "{source:?}");
        }

        let (frozen, frozen_records) = full(source, Some(&records));
        assert_eq!(frozen, green, "{source:?}");
        assert_eq!(frozen_records, records, "{source:?}");
    }
}

#[test]
fn outer_index_close_survives_parenthesized_and_call_nesting() {
    for source in ["a[(f(x ]", "a[(f(@ ]"] {
        let (green, records) = full(source, None);
        let mut expected = vec![];
        if source.contains('@') {
            expected.push(record(
                GrammarRole::Expression(ExpressionRole::CallArgument),
                RecoveryKind::Error,
                5..6,
                UnexpectedCategory::OtherCharacter,
            ));
        }
        expected.push(record(
            Form::Call.closing(),
            RecoveryKind::Missing,
            6..6,
            UnexpectedCategory::OtherCharacter,
        ));
        expected.push(record(
            Form::Group.closing(),
            RecoveryKind::Missing,
            6..6,
            UnexpectedCategory::OtherCharacter,
        ));
        for (index, record) in expected.iter_mut().enumerate() {
            record.id = DiagnosticId(index as u32);
        }
        assert_eq!(records, expected, "{source:?}");
        assert_eq!(green.to_string(), source);
        let root = SyntaxNode::new_root(green.clone());
        let bracket = root
            .descendants_with_tokens()
            .filter_map(|it| it.into_token())
            .find(|it| it.kind() == SyntaxKind::RBracket)
            .unwrap();
        assert_eq!(bracket.parent().unwrap().kind(), SyntaxKind::IndexTail);
        let leading = bracket.prev_token().unwrap();
        assert_eq!(leading.text(), " ");
        assert_eq!(leading.parent().unwrap().kind(), SyntaxKind::IndexTail);
        let (again, frozen) = full(source, Some(&records));
        assert_eq!(again, green);
        assert_eq!(frozen, records);
    }
}

#[test]
fn maximal_runs_preserve_initial_and_internal_leading_and_exact_spread_retry() {
    check(
        "  @ @ x)",
        Form::Call,
        vec![record(
            GrammarRole::Expression(ExpressionRole::CallArgument),
            RecoveryKind::Error,
            2..5,
            UnexpectedCategory::OtherCharacter,
        )],
    );
    check(
        "@ ..x}",
        Form::Record,
        vec![record(
            GrammarRole::Expression(ExpressionRole::ProjectionRecordItem),
            RecoveryKind::Error,
            0..1,
            UnexpectedCategory::OtherCharacter,
        )],
    );
    check(
        "@.. x}",
        Form::Record,
        vec![record(
            GrammarRole::Expression(ExpressionRole::ProjectionRecordItem),
            RecoveryKind::Error,
            0..1,
            UnexpectedCategory::OtherCharacter,
        )],
    );
    check(
        "..@.. x}",
        Form::Record,
        vec![
            record(
                GrammarRole::Expression(ExpressionRole::ProjectionRecordSpreadRhs),
                RecoveryKind::Error,
                2..3,
                UnexpectedCategory::OtherCharacter,
            ),
            record(
                GrammarRole::Expression(ExpressionRole::ProjectionRecordSeparator),
                RecoveryKind::Missing,
                3..3,
                UnexpectedCategory::OtherCharacter,
            ),
        ],
    );
    for source in ["+.. x}", "..+.. x}"] {
        check(
            source,
            Form::Record,
            vec![record(
                GrammarRole::Expression(ExpressionRole::ProjectionRecordItem),
                RecoveryKind::Error,
                0..source.find(' ').unwrap(),
                UnexpectedCategory::OtherCharacter,
            )],
        );
    }
    check(
        ".. +.. x}",
        Form::Record,
        vec![record(
            GrammarRole::Expression(ExpressionRole::ProjectionRecordSpreadRhs),
            RecoveryKind::Error,
            3..6,
            UnexpectedCategory::OtherCharacter,
        )],
    );
    check(
        "x @,)",
        Form::Call,
        vec![record(
            GrammarRole::Expression(ExpressionRole::CallArgumentSeparator),
            RecoveryKind::Error,
            2..3,
            UnexpectedCategory::OtherCharacter,
        )],
    );
    check(
        "x @",
        Form::Call,
        vec![
            record(
                GrammarRole::Expression(ExpressionRole::CallArgumentSeparator),
                RecoveryKind::Error,
                2..3,
                UnexpectedCategory::OtherCharacter,
            ),
            record(
                Form::Call.closing(),
                RecoveryKind::Missing,
                3..3,
                UnexpectedCategory::OtherCharacter,
            ),
        ],
    );
    check(
        " ]",
        Form::Group,
        vec![
            record(
                Form::Group.closing(),
                RecoveryKind::Error,
                0..2,
                UnexpectedCategory::Punctuation(PunctuationEvidence::Close(Delimiter::Bracket)),
            ),
            record(
                Form::Group.closing(),
                RecoveryKind::Missing,
                2..2,
                UnexpectedCategory::OtherCharacter,
            ),
        ],
    );
}

#[test]
fn accepted_delimiters_shield_contextual_stops_and_keep_ml_items() {
    for source in [
        "a(x y)",
        "a[x y]",
        "a.(x y)",
        "a.{x y}",
        "(x,y)",
        "if f({x}): y",
        "if f(x: y): z",
        "f(if x: y)",
        "f(case x: _ -> y)",
        "f({for x in xs: y})",
    ] {
        let (green, records) = full(source, None);
        assert_eq!(green.to_string(), source, "{source:?}");
        assert!(records.is_empty(), "{source:?}: {records:?}");
        assert!(
            !SyntaxNode::new_root(green.clone())
                .descendants_with_tokens()
                .any(|node| matches!(
                    node.kind(),
                    SyntaxKind::Missing | SyntaxKind::Error | SyntaxKind::Invalid
                )),
            "{source:?}"
        );
        let (again, frozen) = full(source, Some(&records));
        assert_eq!(again, green);
        assert_eq!(frozen, records);
    }
}

#[test]
fn quoted_prefix_and_utf8_error_ranges_stay_physical_and_reconcile() {
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
    let source = "@\r\n> > 💥)";
    let (green, exit, remainder, records) = parse(source, Form::Group, 100, Some(&fence), None);
    let role = GrammarRole::Expression(ExpressionRole::Nud);
    let first = record(
        role,
        RecoveryKind::Error,
        100..101,
        UnexpectedCategory::OtherCharacter,
    );
    let mut second = record(
        role,
        RecoveryKind::Error,
        107..111,
        UnexpectedCategory::OtherCharacter,
    );
    second.id = DiagnosticId(1);
    assert_eq!(records, [first, second]);
    assert_eq!(green.to_string(), source);
    assert_eq!(remainder, "");
    assert!(matches!(
        exit,
        NormalizedExit::Complete(Ok(()), LineEntry::InLine)
    ));
    let root = SyntaxNode::new_root(green.clone());
    assert_eq!(
        root.descendants_with_tokens()
            .filter_map(|node| node.into_token())
            .filter(|token| token.kind() == SyntaxKind::YmQuotePrefix)
            .count(),
        1
    );
    assert_eq!(
        crate::tests::recovery_output::recovery_groups(&root)
            .into_iter()
            .map(|node| node.to_string())
            .collect::<Vec<_>>(),
        ["@", "💥"]
    );
    let (again, _, _, frozen) = parse(source, Form::Group, 100, Some(&fence), Some(&records));
    assert_eq!(again, green);
    assert_eq!(frozen, records);
}
