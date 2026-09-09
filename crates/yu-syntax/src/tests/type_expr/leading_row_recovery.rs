use crate::tests::type_expr::*;

pub(super) fn head_error(id: u32, range: Range<usize>) -> CommittedRecoveryRecord {
    expected_type_expression_error(
        id,
        TypeRole::LeadingEffectTypeHead,
        range.clone(),
        Arc::from([UnexpectedSyntax::Token {
            range,
            category: UnexpectedCategory::OtherCharacter,
        }]),
    )
}

fn head_missing(id: u32, at: usize) -> CommittedRecoveryRecord {
    expected_type_expression_missing(id, TypeRole::LeadingEffectTypeHead, at)
}

#[test]
fn leading_row_missing_head_is_distinct_from_incomplete_row_close() {
    for (source, expected) in [
        ("[e]", vec![head_missing(0, 3)]),
        ("[e] ", vec![head_missing(0, 4)]),
        ("F([e] )", vec![head_missing(0, 5)]),
        (
            "[e",
            vec![bracket_recovery::close(0, 2..2, None), head_missing(1, 2)],
        ),
        (
            "F([e)",
            vec![bracket_recovery::close(0, 4..4, None), head_missing(1, 4)],
        ),
    ] {
        let root = assert_complete_type_recovery(source, 0, &expected);
        if source.starts_with('F') {
            let close = root
                .descendants_with_tokens()
                .filter_map(|element| element.into_token())
                .find(|token| token.kind() == SyntaxKind::RParen)
                .unwrap();
            assert_eq!(close.parent().unwrap().kind(), SyntaxKind::TypeCallClose);
            assert_eq!(
                close.parent().unwrap().parent().unwrap().kind(),
                SyntaxKind::TypeCallTail
            );
        }
    }
}

#[test]
fn leading_row_error_retries_one_head_without_a_missing_cascade() {
    for (source, range, text) in [
        ("[e][f]T", 3..6, "[f]"),
        ("[e][/*]*/f]T", 3..11, "[/*]*/f]"),
        ("[e][f", 3..5, "[f"),
        ("[e][f ", 3..5, "[f"),
        ("[e][f][g]T", 3..9, "[f][g]"),
        ("[e] @ [f] T", 4..9, "@ [f]"),
        ("[e][f(A,{x})]T", 3..13, "[f(A,{x})]"),
        ("[e][[a],b;[c]]T", 3..14, "[[a],b;[c]]"),
        ("[e] @ T", 4..5, "@"),
        ("[e] @", 4..5, "@"),
        ("[e] @ ", 4..5, "@"),
        ("[e] @ : T", 4..7, "@ :"),
        ("[e] @/*é*/T", 4..5, "@"),
        ("[e] @\n  T", 4..5, "@"),
        ("[e] @\r\n  T", 4..5, "@"),
        ("[e][a\n  b]T", 3..10, "[a\n  b]"),
    ] {
        let root = assert_complete_type_recovery(source, 0, &[head_error(0, range)]);
        let top = root
            .children()
            .find(|node| node.kind() == SyntaxKind::TypeExpression)
            .unwrap();
        let error = recovery_groups(&top)
            .into_iter()
            .find(|group| group.parent().as_ref() == Some(&top))
            .unwrap();
        assert_eq!(error.text(), text, "{source:?}");
        assert_eq!(
            top.descendants()
                .filter(|node| node.kind() == SyntaxKind::BracketRow)
                .count(),
            1,
            "{source:?}"
        );
        assert!(
            !top.descendants()
                .any(|node| node.kind() == SyntaxKind::Missing),
            "{source:?}"
        );
        if text.starts_with('[') {
            assert_eq!(error.first_token().unwrap().kind(), SyntaxKind::Error);
            assert_eq!(error.first_token().unwrap().text(), "[");
        }
        if text.ends_with(']') {
            assert_eq!(error.last_token().unwrap().kind(), SyntaxKind::Error);
            assert_eq!(error.last_token().unwrap().text(), "]");
        }
    }
    assert_complete_type_recovery("[e][f]T", 40, &[head_error(0, 43..46)]);
}

#[test]
fn leading_row_boundaries_preserve_the_entire_pending_item_at_every_depth() {
    for (prefix, expected) in [
        ("[e]", head_missing(0, 3)),
        ("[e] @", head_error(0, 4..5)),
        ("[e][bad", head_error(0, 3..7)),
        ("[e][f(bad", head_error(0, 3..9)),
    ] {
        for (suffix, stops) in [
            (" with tail", crate::lexical::stops::STOP_WITH),
            (" /*é*/else tail", crate::lexical::stops::STOP_ELSE),
            (" : tail", STOP_COLON),
            (" , tail", crate::lexical::stops::STOP_COMMA),
            (" } tail", 0),
            ("\nT tail", 0),
            ("\r\nT tail", 0),
        ] {
            let source = format!("{prefix}{suffix}");
            let frozen = frozen_recovery_ids(std::slice::from_ref(&expected));
            for (input, records) in [
                (None, std::slice::from_ref(&expected)),
                (Some(frozen.as_slice()), frozen.as_slice()),
            ] {
                let run = run_contextual_type_snapshot(
                    &source,
                    crate::type_expr::TypeMlContext::INACTIVE,
                    stops,
                    0,
                    0,
                    LineEntry::InLine,
                    None,
                    input,
                );
                assert_eq!(run.green.to_string(), format!("sentinel{prefix}"));
                assert_eq!(run.records, records, "{source:?}");
                assert_eq!(run.slots, 1);
                let NormalizedExit::Complete(Err(Either::Left(pending)), line) = run.exit else {
                    panic!("head boundary stays pending: {source:?}")
                };
                let (control, origin, control_line, remainder, _, _) =
                    scan_type_item_control(suffix, prefix.len(), &OperatorTable::empty());
                assert_eq!(pending, control, "{source:?}");
                assert_eq!(run.successor_origin, origin);
                assert_eq!(run.remainder, remainder);
                assert_eq!(line, control_line);
                assert_eq!(run.mark, ());
                assert!(run.same_operators);
            }
        }
    }
}

#[test]
fn leading_row_contextual_outer_boundary_survives_malformed_nesting() {
    let source = "[e][bad with tail";
    let expected = [head_error(0, 3..7)];
    let (green, exit, found, _, remainder, records, _, _) =
        run_required_type_with_outer_boundary_and_recoveries(
            source,
            crate::type_expr::TypeOuterBoundary::WITH,
            false,
            None,
        );
    assert!(found);
    assert_eq!(green.to_string(), "[e][bad");
    assert_eq!(records, expected);
    assert_eq!(remainder, " tail");
    let NormalizedExit::Complete(Err(Either::Left(pending)), _) = exit else {
        panic!("outer contextual boundary stays pending")
    };
    assert_eq!(pending.payload_view().spelling(), Some("with"));
    assert!(!pending.leading_view().is_grammar_empty());
}

#[test]
fn leading_row_fences_preserve_unemitted_newline_and_comment_carriers() {
    let fence = FenceBoundary {
        opener: FenceOpener {
            line: 0,
            marker: 0..3,
            marker_width: 3,
        },
        prefix_policy: FencePrefixPolicy::ActivePrefixQuote { depth: 2, base: 0 },
        close_column: 0,
    };
    for (prefix, leading, expected) in [
        ("> > [e]", "\n", head_missing(0, 8)),
        ("> > [e] @", "\n", head_error(0, 8..9)),
        ("> > [e] [bad", "\r\n", head_error(0, 8..12)),
        ("> > [e] [bad", "/*\n> > still\n", head_error(0, 8..12)),
    ] {
        let source = format!("{prefix}{leading}> > ```\nouter]");
        let frozen = frozen_recovery_ids(std::slice::from_ref(&expected));
        for (input, records) in [
            (None, std::slice::from_ref(&expected)),
            (Some(frozen.as_slice()), frozen.as_slice()),
        ] {
            let (green, exit, remainder, actual) = run_type_normalized_with_recoveries(
                &source,
                0,
                LineEntry::PhysicalStart,
                Some(&fence),
                input,
            );
            assert_eq!(green.to_string(), prefix, "{source:?}");
            assert_eq!(actual, records, "{source:?}");
            assert_eq!(remainder, "> > ```\nouter]");
            let Some(NormalizedExit::Complete(
                Err(Either::Left(pending)),
                LineEntry::PhysicalStart,
            )) = exit
            else {
                panic!("head preserves fence")
            };
            assert_eq!(
                pending
                    .payload_view()
                    .pending_boundary()
                    .unwrap()
                    .coordinate(),
                prefix.len() + leading.len()
            );
            let mut output = GreenNodeBuilder::new();
            output.start_node(SyntaxKind::Root.into());
            pending.emit_terminal_boundary(&mut output);
            output.finish_node();
            let tail = output.finish();
            assert_eq!(tail.to_string(), leading, "{source:?}");
            if leading.contains("still") {
                assert!(
                    SyntaxNode::new_root(tail)
                        .descendants_with_tokens()
                        .any(|element| element.kind() == SyntaxKind::YmQuotePrefix)
                );
            }
        }
    }
}

#[test]
fn leading_row_structured_tag_errors_reserve_before_nested_head_records() {
    for (source, extent, head) in [
        (":{[e]}", 2..5, head_missing(1, 5)),
        (":{[e][f]T}", 2..9, head_error(1, 5..8)),
    ] {
        assert_complete_type_recovery(
            source,
            0,
            &[
                expected_type_error(0, TypeRole::PolymorphicVariantTagName, extent),
                head,
            ],
        );
    }
}

#[test]
fn leading_row_accepted_heads_keep_attachment_and_primary_disposition() {
    for source in [
        "[e] T",
        "[e] F [io] -> U",
        "[e] for 'a: T",
        "[e] :{A}",
        "[e] '[io]",
        "[e] {a: A}",
        "[e] (A)",
        "[e]\n  T",
        "[e]\r\n  T",
    ] {
        let root = assert_complete_type_recovery(source, 0, &[]);
        assert!(!root.descendants_with_tokens().any(|node| matches!(
            node.kind(),
            SyntaxKind::Missing | SyntaxKind::Error | SyntaxKind::Invalid
        )));
        let top = root
            .children()
            .find(|node| node.kind() == SyntaxKind::TypeExpression)
            .unwrap();
        assert!(
            top.children()
                .any(|node| node.kind() == SyntaxKind::BracketRow)
        );
        assert!(
            !top.children()
                .any(|node| node.kind() == SyntaxKind::TypeExpression)
        );
    }
}
