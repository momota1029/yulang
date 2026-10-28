use crate::tests::type_expr::required_recovery::run_statement_structural_facts;
use crate::tests::type_expr::*;
use crate::{
    ambient_claim::AmbientClaimView,
    declaration::fields::{FieldList, FieldOuterClose, declaration_fields_normalized},
    type_expr::{TypeOuterBoundary, type_nud_item_normalized},
};
fn equals_error(_: u32, start: usize, text: &str) -> ExpectedStructural {
    match text {
        "=" | "@ =" | "= =" => (StructuralKind::ErrorGroup, start..start + text.len()),
        _ => panic!("explicit Equals recovery witness"),
    }
}

fn field_separator_missing(at: usize) -> ExpectedStructural {
    (StructuralKind::Missing, at..at)
}

fn field_close_missing(at: usize) -> ExpectedStructural {
    (StructuralKind::Missing, at..at)
}

fn field_type_missing(_: u32, at: usize) -> ExpectedStructural {
    (StructuralKind::Missing, at..at)
}

#[test]
fn required_type_unclaimed_equals_consumes_and_retries_one_primary() {
    // One callee attempt is bounded even before the fix; entering the old
    // tuple field loop with this pending Equals would retry without progress.
    let (green, exit, found, remainder, facts) =
        run_required_type_with_structural_diagnostics("=A", 0, LineEntry::InLine, None);
    assert_eq!(green.to_string(), "=A");
    assert_eq!(remainder, "");
    assert!(found);
    assert!(matches!(
        exit,
        NormalizedExit::Complete(Err(Either::Right(_)), LineEntry::InLine)
    ));
    assert_eq!(facts, [(StructuralKind::ErrorGroup, 0..1)]);
}

#[test]
fn required_type_claimed_equals_stays_pending_before_and_after_recovery() {
    for (source, emitted, expected, gap, suffix_start) in [
        ("=A", "", (StructuralKind::Missing, (0)..(0)), "", 0),
        ("@ =A", "@", (StructuralKind::ErrorGroup, 0..1), " ", 1),
    ] {
        let (green, exit, found, next, remainder, facts) =
            run_required_type_with_outer_boundary_and_structural_diagnostics(
                source,
                TypeOuterBoundary::EQUALS,
                false,
            );
        assert_eq!(green.to_string(), emitted);
        assert!(!found);
        assert_eq!(facts, [expected.clone()]);
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
                let expected = if raw_missing == 1 {
                    vec![
                        field_separator_missing("sentinel".len() + local_start),
                        equals_error(1, "sentinel".len() + local_start, malformed),
                    ]
                } else {
                    vec![equals_error(0, "sentinel".len() + local_start, malformed)]
                };
                let fresh = run_statement_structural_facts(&source, origin);
                assert_eq!(fresh.green.to_string(), format!("sentinel{source}"));
                assert_eq!(fresh.remainder, "", "{source:?}");
                assert_eq!(fresh.successor_origin, origin + source.len());
                assert_eq!(fresh.facts, expected, "{source:?}");
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
                let errors = recovery_groups(&root).into_iter().collect::<Vec<_>>();
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
                    assert_eq!(token.kind(), SyntaxKind::Error);
                }
            }
        }
    }
}

fn run_tuple<'source>(
    source: &'source str,
    origin: usize,
    fence: Option<&FenceBoundary>,
) -> ContextualTypeRun<'source> {
    let operators = OperatorTable::empty();
    let mut input = source;
    let mut recover = Recover::new_for_test(&operators);
    let mark = crate::cursor::LexRecover::new_for_test(recover.operators()).mark();
    let mut output = GreenNodeBuilder::new();
    output.start_node(SyntaxKind::Root.into());
    seed_identifier(&mut output);
    output.start_node(SyntaxKind::Missing.into());
    output.finish_node();
    let (open, next, line) = type_nud_item_normalized(
        crate::cursor::SyntaxIn::new(&mut input, &mut recover, &mut output),
        origin,
        LineEntry::InLine,
        fence,
    );
    let result = declaration_fields_normalized(
        crate::cursor::SyntaxIn::new(&mut input, &mut recover, &mut output),
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
    output.finish_node();
    let same_operators = std::ptr::eq(recover.operators(), &operators);
    let green = finish_with_discarded_recoveries(output, recover);
    let facts = structural_facts(&green);
    assert_eq!(result.item_origin, origin + source.len() - input.len());
    ContextualTypeRun {
        green,
        exit: result.exit,
        successor_origin: result.item_origin,
        remainder: input,
        facts,
        mark,
        same_operators,
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
            let mut expected = vec![
                (StructuralKind::Missing, "sentinel".len().."sentinel".len()),
                equals_error(1, "sentinel".len() + 1, "="),
            ];
            if source.contains(']') {
                expected.push(field_close_missing("sentinel".len() + 2));
            }
            if fence.is_some() {
                expected.push(field_type_missing(2, "sentinel".len() + 2));
                expected.push(field_close_missing("sentinel".len() + 2));
            }
            let fresh = run_tuple(source, origin, fence);
            assert_eq!(
                fresh.green.to_string(),
                format!("sentinel{emitted}"),
                "{source:?}"
            );
            assert_eq!(fresh.facts, expected, "{source:?}");
            assert_eq!(fresh.remainder, remainder);
            assert_eq!(fresh.successor_origin, origin + next);
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
                let mut recover = Recover::new_for_test(&operators);
                let mut output = GreenNodeBuilder::new();
                let (control, control_next, control_line) = type_nud_item_normalized(
                    crate::cursor::SyntaxIn::new(&mut control_input, &mut recover, &mut output),
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
            let result = run_statement_structural_facts(&source, 0);
            assert_eq!(result.green.to_string(), format!("sentinel{source}"));
            assert_eq!(result.remainder, "");
            assert!(result.facts.is_empty());
            let root = SyntaxNode::new_root(result.green);
            assert_eq!(
                root.descendants()
                    .filter(|node| node.kind() == SyntaxKind::StructField)
                    .count(),
                usize::from(body != "()"),
                "{source:?}\n{root:#?}"
            );
            assert!(
                !root.descendants_with_tokens().any(|node| matches!(
                    node.kind(),
                    SyntaxKind::Missing | SyntaxKind::Error | SyntaxKind::Invalid
                )),
                "{source:?}\n{root:#?}"
            );
        }
    }
}
