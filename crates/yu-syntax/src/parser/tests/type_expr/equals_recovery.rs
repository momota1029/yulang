use super::required_recovery::{assert_same_exit, missing, run_statement_records};
use super::*;
use crate::{
    parser::{
        ambient_claim::AmbientClaimView,
        struct_decl::{FieldList, FieldOuterClose, declaration_fields_normalized},
        type_expr::{TypeOuterBoundary, type_nud_item_normalized},
    },
    session::{DeclarationRole, StructRole},
};

fn equals_error(id: u32, start: usize, text: &str) -> CommittedRecoveryRecord {
    let equals = UnexpectedCategory::Punctuation(PunctuationEvidence::Equals);
    let parts = match text {
        "=" => vec![(0..1, equals)],
        "@ =" => vec![(0..1, UnexpectedCategory::OtherCharacter), (1..3, equals)],
        "= =" => vec![(0..1, equals), (1..3, equals)],
        _ => panic!("explicit Equals recovery witness"),
    };
    expected_required_type_primary_error(
        id,
        start..start + text.len(),
        parts
            .into_iter()
            .map(|(range, category)| UnexpectedSyntax::Token {
                range: start + range.start..start + range.end,
                category,
            })
            .collect::<Vec<_>>()
            .into(),
    )
}

#[test]
fn required_type_unclaimed_equals_consumes_and_retries_one_primary() {
    // One callee attempt is bounded even before the fix; entering the old
    // tuple field loop with this pending Equals would retry without progress.
    let (green, exit, found, remainder, records) =
        run_required_type_with_recoveries("=A", 0, LineEntry::InLine, None, None);
    assert_eq!(green.to_string(), "=A");
    assert_eq!(remainder, "");
    assert!(found);
    assert!(matches!(
        exit,
        NormalizedExit::Complete(Err(Either::Right(_)), LineEntry::InLine)
    ));
    assert_eq!(
        records,
        [expected_required_type_primary_error(
            0,
            0..1,
            Arc::from([UnexpectedSyntax::Token {
                range: 0..1,
                category: UnexpectedCategory::Punctuation(PunctuationEvidence::Equals),
            }]),
        )]
    );
}

#[test]
fn required_type_claimed_equals_stays_pending_before_and_after_recovery() {
    for (source, emitted, expected, gap, suffix_start) in [
        (
            "=A",
            "",
            expected_type_expression_missing(0, TypeRole::Primary, 0),
            "",
            0,
        ),
        (
            "@ =A",
            "@",
            expected_required_type_primary_error(
                0,
                0..1,
                Arc::from([UnexpectedSyntax::Token {
                    range: 0..1,
                    category: UnexpectedCategory::OtherCharacter,
                }]),
            ),
            " ",
            1,
        ),
    ] {
        let (green, exit, found, next, remainder, records, slots, diagnostics) =
            run_required_type_with_outer_boundary_and_recoveries(
                source,
                TypeOuterBoundary::EQUALS,
                false,
                None,
            );
        assert_eq!(green.to_string(), emitted);
        assert!(!found);
        assert_eq!(records, [expected.clone()]);
        assert_eq!(slots, 1);
        assert_eq!(diagnostics, (Some(1), 0));
        let (mut control, control_next, control_line, control_remainder, _, _) =
            scan_type_item_control(
                &source[suffix_start..],
                suffix_start,
                &OperatorTable::empty(),
            );
        let NormalizedExit::Complete(Err(Either::Left(item)), line) = &exit else {
            panic!("caller-owned Equals remains pending")
        };
        assert_eq!(item, &control);
        assert_eq!(*line, control_line);
        assert_eq!(next, control_next);
        assert_eq!(remainder, control_remainder);
        assert_eq!(emit_pending_leading_text(&mut control), gap);
        let frozen = frozen_recovery_ids(&[expected]);
        let (
            replayed,
            replay_exit,
            replay_found,
            replay_next,
            replay_remainder,
            records,
            slots,
            diagnostics,
        ) = run_required_type_with_outer_boundary_and_recoveries(
            source,
            TypeOuterBoundary::EQUALS,
            false,
            Some(&frozen),
        );
        assert_eq!(replayed, green);
        assert_same_exit(&exit, &replay_exit);
        assert_eq!(replay_found, found);
        assert_eq!(replay_next, next);
        assert_eq!(replay_remainder, remainder);
        assert_eq!(records, frozen);
        assert_eq!(slots, 1);
        assert_eq!(diagnostics, (Some(8), 1));
    }
}

#[test]
fn declaration_fields_recover_unclaimed_equals_without_zero_progress_retry() {
    for origin in [0, 41] {
        for (body, malformed, fields, raw_missing) in [
            ("(=)", "=", 1, 0),
            ("(=T)", "=", 1, 0),
            ("(A,=T)", "=", 2, 0),
            ("(@ =T)", "@ =", 1, 0),
            ("(=,T)", "=", 2, 0),
            ("(= =T)", "= =", 1, 0),
            // The existing field-separator slot is separate and still raw.
            ("(A =T)", "=", 2, 1),
            ("{a:=T}", "=", 1, 0),
            ("{a:@ =T}", "@ =", 1, 0),
            ("{a: = =T}", "= =", 1, 0),
            ("{a:=}", "=", 1, 0),
        ] {
            for source in [
                format!("struct S{body}"),
                format!("enum E {{A{body}}}"),
                format!("error E {{A{body}}}"),
            ] {
                let local_start = source.find(malformed).unwrap();
                let expected = [equals_error(0, origin + local_start, malformed)];
                let fresh = run_statement_records(&source, origin, None);
                assert_eq!(fresh.green.to_string(), format!("sentinel{source}"));
                assert_eq!(fresh.remainder, "", "{source:?}");
                assert_eq!(fresh.successor_origin, origin + source.len());
                assert_eq!(fresh.records, expected, "{source:?}");
                assert_eq!(fresh.slots, 1);
                assert_eq!(fresh.diagnostics, (Some(1), 0));
                assert_eq!(fresh.mark, ());
                assert!(fresh.same_operators);
                let root = SyntaxNode::new_root(fresh.green.clone());
                assert_eq!(
                    root.descendants()
                        .filter(|node| node.kind() == SyntaxKind::StructField)
                        .count(),
                    fields,
                    "{source:?}\n{root:#?}"
                );
                assert_eq!(
                    root.descendants()
                        .filter(|node| node.kind() == SyntaxKind::Missing)
                        .count(),
                    raw_missing,
                    "{source:?}\n{root:#?}"
                );
                let errors = root
                    .descendants()
                    .filter(|node| node.kind() == SyntaxKind::Error)
                    .collect::<Vec<_>>();
                assert_eq!(errors.len(), 1, "{source:?}\n{root:#?}");
                assert_eq!(errors[0].to_string(), malformed);
                assert_eq!(errors[0].parent().unwrap().kind(), SyntaxKind::StructField);
                assert_eq!(
                    usize::from(errors[0].text_range().start()),
                    "sentinel".len() + local_start
                );
                assert_eq!(
                    usize::from(errors[0].text_range().end()),
                    "sentinel".len() + local_start + malformed.len()
                );
                for token in errors[0]
                    .descendants_with_tokens()
                    .filter_map(|element| element.into_token())
                    .filter(|token| token.text() == "=")
                {
                    assert_eq!(token.kind(), SyntaxKind::Equals);
                }
                let frozen = frozen_recovery_ids(&expected);
                let replay = run_statement_records(&source, origin, Some(&frozen));
                assert_eq!(replay.green, fresh.green);
                assert_eq!(replay.records, frozen);
                assert_same_exit(&fresh.exit, &replay.exit);
                assert_eq!(replay.successor_origin, fresh.successor_origin);
                assert_eq!(replay.remainder, fresh.remainder);
                assert_eq!(replay.slots, 1);
                assert_eq!(replay.diagnostics, (Some(8), 1));
            }
        }
    }
}

fn run_tuple<'source>(
    source: &'source str,
    origin: usize,
    fence: Option<&FenceBoundary>,
    frozen: Option<&[CommittedRecoveryRecord]>,
) -> ContextualTypeRun<'source> {
    let operators = OperatorTable::empty();
    let mut input = source;
    let mut recover = Recover::new(&operators);
    let mark = recover.mark();
    let mut output = frozen.map_or_else(GreenNodeBuilder::new, GreenNodeBuilder::reconcile);
    output.start_node(SyntaxKind::Root.into());
    seed_identifier(&mut output);
    output.start_node(SyntaxKind::Missing.into());
    output.finish_node();
    commit_record_draft(
        &mut output,
        &missing(0, GrammarRole::Type(TypeRole::ArrowRhs), origin),
    );
    let (open, next, line) = type_nud_item_normalized(
        In::new(&mut input, &mut recover, &mut output),
        origin,
        LineEntry::InLine,
        fence,
    );
    let result = declaration_fields_normalized(
        In::new(&mut input, &mut recover, &mut output),
        GrammarRole::Declaration(DeclarationRole::Struct(StructRole::FieldType)),
        open,
        0,
        0,
        FieldList::Tuple,
        FieldOuterClose::Borrow,
        false,
        next,
        line,
        fence,
        Some(AmbientClaimView::root_statement(0)).into(),
    );
    let slots = output.recovery_slot_count();
    let diagnostics = output.diagnostic_position();
    output.finish_node();
    let (green, records) = output.finish_with_recoveries();
    assert_eq!(result.item_origin, origin + source.len() - input.len());
    ContextualTypeRun {
        green,
        exit: result.exit,
        successor_origin: result.item_origin,
        remainder: input,
        records,
        slots,
        diagnostics,
        mark,
        same_operators: std::ptr::eq(recover.operators(), &operators),
    }
}

#[test]
fn tuple_equals_recovery_preserves_seeded_output_and_complete_close_or_fence_item() {
    let fence = FenceBoundary {
        opener: FenceOpener {
            line: 0,
            marker: 0..3,
            marker_width: 3,
        },
        prefix_policy: FencePrefixPolicy::ActivePrefixQuote { depth: 2, base: 0 },
        close_column: 0,
    };
    for origin in [0, 41] {
        for (source, emitted, remainder, next, fence) in [
            ("(=)tail", "(=)", "tail", 3, None),
            ("(= )tail", "(= )", "tail", 4, None),
            ("(= ]tail", "(=", "tail", 4, None),
            ("(=", "(=", "", 2, None),
            (
                "(=\r\n> > ```\nouter",
                "(=",
                "> > ```\nouter",
                4,
                Some(&fence),
            ),
        ] {
            let expected = [
                missing(0, GrammarRole::Type(TypeRole::ArrowRhs), origin),
                equals_error(1, origin + 1, "="),
            ];
            let fresh = run_tuple(source, origin, fence, None);
            assert_eq!(
                fresh.green.to_string(),
                format!("sentinel{emitted}"),
                "{source:?}"
            );
            assert_eq!(fresh.records, expected, "{source:?}");
            assert_eq!(fresh.remainder, remainder);
            assert_eq!(fresh.successor_origin, origin + next);
            assert_eq!(fresh.slots, 2);
            assert_eq!(fresh.diagnostics, (Some(2), 0));
            assert_eq!(fresh.mark, ());
            assert!(fresh.same_operators);
            if emitted.ends_with(')') {
                assert!(matches!(
                    fresh.exit,
                    NormalizedExit::Complete(Ok(()), LineEntry::InLine)
                ));
            } else {
                let mut control_input = &source[2..];
                let operators = OperatorTable::empty();
                let mut recover = Recover::new(&operators);
                let mut output = GreenNodeBuilder::new();
                let (control, control_next, control_line) = type_nud_item_normalized(
                    In::new(&mut control_input, &mut recover, &mut output),
                    origin + 2,
                    LineEntry::InLine,
                    fence,
                );
                match &fresh.exit {
                    NormalizedExit::Complete(Err(Either::Left(item)), line) => {
                        assert_eq!(item, &control);
                        assert_eq!(*line, control_line);
                    }
                    NormalizedExit::Complete(Err(Either::Right(end)), line) => {
                        assert_eq!(end.item, control);
                        assert_eq!(*line, control_line);
                    }
                    _ => panic!("complete borrowed close or boundary Item"),
                }
                assert_eq!(fresh.successor_origin, control_next);
                assert_eq!(fresh.remainder, control_input);
            }
            let frozen = frozen_recovery_ids(&expected);
            let replay = run_tuple(source, origin, fence, Some(&frozen));
            assert_eq!(replay.green, fresh.green);
            assert_eq!(replay.records, frozen);
            assert_eq!(replay.slots, 2);
            assert_eq!(replay.diagnostics, (Some(9), 2));
            assert_same_exit(&fresh.exit, &replay.exit);
            assert_eq!(replay.successor_origin, fresh.successor_origin);
            assert_eq!(replay.remainder, fresh.remainder);
        }
    }
}

#[test]
fn declaration_field_equals_fix_retains_accepted_type_apply_and_trailing_comma() {
    for body in ["()", "(A B)", "(A,)", "{a:T}"] {
        for source in [
            format!("struct S{body}"),
            format!("enum E {{A{body}}}"),
            format!("error E {{A{body}}}"),
        ] {
            let result = run_statement_records(&source, 0, None);
            assert_eq!(result.green.to_string(), format!("sentinel{source}"));
            assert_eq!(result.remainder, "");
            assert!(result.records.is_empty());
            let root = SyntaxNode::new_root(result.green);
            assert_eq!(
                root.descendants()
                    .filter(|node| node.kind() == SyntaxKind::StructField)
                    .count(),
                usize::from(body != "()"),
                "{source:?}\n{root:#?}"
            );
            assert!(
                !root
                    .descendants()
                    .any(|node| matches!(node.kind(), SyntaxKind::Missing | SyntaxKind::Error)),
                "{source:?}\n{root:#?}"
            );
        }
    }
}
