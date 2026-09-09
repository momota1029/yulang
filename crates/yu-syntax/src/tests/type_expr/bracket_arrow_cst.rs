//! Rowan evidence for the required arrow selected by a trailing BracketRow.
use super::*;

fn tail(root: &SyntaxNode) -> SyntaxNode {
    root.descendants()
        .find(|node| node.kind() == SyntaxKind::TypeArrowTail)
        .unwrap()
}

fn children(node: &SyntaxNode) -> Vec<(SyntaxKind, String)> {
    node.children_with_tokens()
        .map(|child| (child.kind(), child.to_string()))
        .collect()
}

#[test]
fn bracket_arrow_cst_orders_arrowless_actual_arrow_and_eof_slots() {
    use SyntaxKind::*;
    for (source, suffix) in [
        (
            "F [e] -> U",
            vec![(Whitespace, " "), (Arrow, "->"), (TypeExpression, " U")],
        ),
        (
            "F [e] U",
            vec![(Whitespace, " "), (Missing, ""), (TypeExpression, "U")],
        ),
        ("F [e] ", vec![(Whitespace, " "), (Missing, "")]),
        ("F [e]", vec![(Missing, "")]),
    ] {
        let (green, _) = run_type(source);
        assert_eq!(green.to_string(), source);
        let root = SyntaxNode::new_root(green);
        let owner = tail(&root);
        let expected = std::iter::once((BracketRow, "[e]"))
            .chain(suffix)
            .map(|(kind, text)| (kind, text.to_owned()))
            .collect::<Vec<_>>();
        assert_eq!(children(&owner), expected, "{source:?}");
        let before = owner.prev_sibling_or_token().unwrap();
        assert_eq!(
            (before.kind(), before.to_string()),
            (Whitespace, " ".into())
        );
    }
}

#[test]
fn bracket_arrow_cst_error_group_ends_before_retry_trivia_and_never_cascades() {
    use SyntaxKind::*;
    for (source, run, suffix) in [
        (
            "F [e] @ -> U",
            "@",
            vec![(Whitespace, " "), (Arrow, "->"), (TypeExpression, " U")],
        ),
        (
            "F [e] @ U",
            "@",
            vec![(Whitespace, " "), (TypeExpression, "U")],
        ),
        (
            "F [e] @ : U",
            "@ :",
            vec![(Whitespace, " "), (TypeExpression, "U")],
        ),
        (
            "F [e] @/*é*/-> U",
            "@",
            vec![
                (BlockComment, "/*é*/"),
                (Arrow, "->"),
                (TypeExpression, " U"),
            ],
        ),
        (
            "F [e] @/*é*/: U",
            "@/*é*/:",
            vec![(Whitespace, " "), (TypeExpression, "U")],
        ),
        ("F [e] @ ", "@", vec![(Whitespace, " ")]),
        (
            "F [e] @ ->",
            "@",
            vec![(Whitespace, " "), (Arrow, "->"), (Missing, "")],
        ),
    ] {
        let (green, _) = run_type(source);
        assert_eq!(green.to_string(), source);
        let root = SyntaxNode::new_root(green);
        let owner = tail(&root);
        let direct = owner.children_with_tokens().collect::<Vec<_>>();
        assert_eq!(
            (direct[0].kind(), direct[0].to_string()),
            (BracketRow, "[e]".into())
        );
        assert_eq!(
            (direct[1].kind(), direct[1].to_string()),
            (Whitespace, " ".into())
        );
        let errors = direct[2..]
            .iter()
            .take_while(|child| child.kind() == Error)
            .collect::<Vec<_>>();
        assert!(!errors.is_empty());
        assert!(errors.iter().all(|child| child.as_token().is_some()));
        assert_eq!(
            errors
                .iter()
                .map(|child| child.to_string())
                .collect::<String>(),
            run
        );
        if source == "F [e] @/*é*/: U" {
            assert_eq!(
                errors
                    .iter()
                    .map(|child| (
                        child.to_string(),
                        usize::from(child.text_range().start())
                            ..usize::from(child.text_range().end())
                    ))
                    .collect::<Vec<_>>(),
                [
                    ("@".into(), 6..7),
                    ("/*é*/".into(), 7..13),
                    (":".into(), 13..14)
                ]
            );
            let (shifted, _, _) = run_type_normalized(source, 41, LineEntry::InLine, None);
            let shifted = SyntaxNode::new_root(shifted);
            // Rowan ranges are local to the emitted root, not the scanner origin.
            assert_eq!(shifted.green(), root.green());
        }
        assert_eq!(
            direct[2 + errors.len()..]
                .iter()
                .map(|child| (child.kind(), child.to_string()))
                .collect::<Vec<_>>(),
            suffix
                .into_iter()
                .map(|(kind, text)| (kind, text.to_owned()))
                .collect::<Vec<_>>(),
            "{source:?}"
        );
        assert!(!owner.descendants().any(|node| node.kind() == Invalid));
    }
}

#[test]
fn bracket_arrow_cst_incomplete_row_has_nested_close_and_direct_arrow_missing() {
    for source in ["F [A", "F(T [A)"] {
        let (green, _) = run_type(source);
        assert_eq!(green.to_string(), source);
        let root = SyntaxNode::new_root(green);
        let owner = tail(&root);
        let row = owner
            .children()
            .find(|node| node.kind() == SyntaxKind::BracketRow)
            .unwrap();
        let close = row
            .children()
            .find(|node| node.kind() == SyntaxKind::Missing)
            .unwrap();
        let arrow = owner
            .children()
            .find(|node| node.kind() == SyntaxKind::Missing)
            .unwrap();
        assert_eq!(close.text_range(), arrow.text_range());
        assert!(close.text_range().is_empty());
        assert_eq!(
            children(&owner),
            [
                (SyntaxKind::BracketRow, "[A".into()),
                (SyntaxKind::Missing, "".into())
            ]
        );
        assert_eq!(
            owner
                .descendants()
                .filter(|node| node.kind() == SyntaxKind::Missing)
                .count(),
            2
        );
    }
}

#[test]
fn bracket_arrow_cst_protected_items_keep_complete_leading_before_and_after_error() {
    for head in ["F [e]", "F [e] @"] {
        for (suffix, stops) in [
            (" , tail", 0),
            (" ) tail", 0),
            (" : tail", STOP_COLON),
            (" /*é*/with tail", crate::lexical::stops::STOP_WITH),
        ] {
            let source = format!("{head}{suffix}");
            let run = run_contextual_type_snapshot(
                &source,
                crate::type_expr::TypeMlContext::INACTIVE,
                stops,
                0,
                0,
                LineEntry::InLine,
                None,
                None,
            );
            let NormalizedExit::Complete(Err(Either::Left(pending)), line) = run.exit else {
                panic!("protected Item")
            };
            let (control, origin, control_line, remainder, _, _) =
                scan_type_item_control(suffix, head.len(), &OperatorTable::empty());
            assert_eq!(pending, control);
            assert_eq!(
                (run.successor_origin, line, run.remainder),
                (origin, control_line, remainder)
            );
            let root = SyntaxNode::new_root(run.green);
            assert_eq!(root.to_string(), format!("sentinel{head}"));
            let owner = tail(&root);
            let expected = if head.ends_with('@') {
                vec![
                    (SyntaxKind::BracketRow, "[e]".into()),
                    (SyntaxKind::Whitespace, " ".into()),
                    (SyntaxKind::Error, "@".into()),
                ]
            } else {
                vec![
                    (SyntaxKind::BracketRow, "[e]".into()),
                    (SyntaxKind::Missing, "".into()),
                ]
            };
            assert_eq!(children(&owner), expected);
        }
        let source = format!("{head} with tail");
        let (green, exit, accepted, origin, remainder, _, _, _) =
            run_required_type_with_outer_boundary_and_recoveries(
                &source,
                crate::type_expr::TypeOuterBoundary::WITH,
                false,
                None,
            );
        assert!(accepted);
        assert_eq!(green.to_string(), head);
        let NormalizedExit::Complete(Err(Either::Left(pending)), line) = exit else {
            panic!("outer boundary")
        };
        let (control, control_origin, control_line, control_remainder, _, _) =
            scan_type_item_control(" with tail", head.len(), &OperatorTable::empty());
        assert_eq!(pending, control);
        assert_eq!(
            (origin, line, remainder),
            (control_origin, control_line, control_remainder)
        );
        let root = SyntaxNode::new_root(green);
        assert_eq!(
            children(&tail(&root)).last(),
            Some(&(
                if head.ends_with('@') {
                    SyntaxKind::Error
                } else {
                    SyntaxKind::Missing
                },
                if head.ends_with('@') {
                    "@".into()
                } else {
                    "".into()
                }
            ))
        );
    }
}

#[test]
fn bracket_arrow_cst_layout_protects_shallow_equal_and_retries_deeper() {
    for newline in ["\n", "\r\n"] {
        for indent in [" ", "  ", "   "] {
            for head in ["F [e]", "F [e] @"] {
                let source = format!("{head}{newline}{indent}U");
                let operators = OperatorTable::empty();
                let mut input = source.as_str();
                let mut recover = Recover::new_for_test(&operators);
                let mut output = GreenNodeBuilder::new();
                output.start_node(SyntaxKind::Root.into());
                let (item, origin, line) = crate::type_expr::type_nud_item_normalized(
                    crate::cursor::SyntaxIn::new(&mut input, &mut recover, &mut output),
                    0,
                    LineEntry::InLine,
                    None,
                );
                let (exit, accepted) = crate::type_expr::required_type_expr_with_caller_stops_and_outer_boundary_normalized(crate::cursor::SyntaxIn::new(&mut input, &mut recover, &mut output), item, 2, 0, crate::type_expr::TypeOuterBoundary::NONE, origin, line, None);
                assert!(accepted);
                output.finish_node();
                let root = SyntaxNode::new_root(finish_with_discarded_recoveries(output, recover));
                let owner = tail(&root);
                let mut expected = vec![(SyntaxKind::BracketRow, "[e]".into())];
                if head.ends_with('@') {
                    expected.extend([
                        (SyntaxKind::Whitespace, " ".into()),
                        (SyntaxKind::Error, "@".into()),
                    ]);
                }
                if indent.len() > 2 {
                    expected.extend([
                        (SyntaxKind::Newline, newline.into()),
                        (SyntaxKind::Whitespace, indent.into()),
                    ]);
                    if !head.ends_with('@') {
                        expected.push((SyntaxKind::Missing, "".into()));
                    }
                    expected.push((SyntaxKind::TypeExpression, "U".into()));
                    assert_eq!(root.to_string(), source);
                } else {
                    if !head.ends_with('@') {
                        expected.push((SyntaxKind::Missing, "".into()));
                    }
                    let NormalizedExit::Complete(Err(Either::Left(mut pending)), _) = exit else {
                        panic!("protected newline")
                    };
                    assert_eq!(
                        emit_pending_leading_text(&mut pending),
                        format!("{newline}{indent}")
                    );
                    assert_eq!(pending.payload_view().spelling(), Some("U"));
                    assert_eq!(root.to_string(), head);
                }
                assert_eq!(children(&owner), expected, "{source:?}");
            }
        }
    }
}

#[test]
fn bracket_arrow_cst_fence_preserves_abstract_coordinate_and_pending_leading() {
    let fence = FenceBoundary {
        opener: FenceOpener {
            line: 0,
            marker: 0..3,
            marker_width: 3,
        },
        prefix_policy: FencePrefixPolicy::ActivePrefixQuote { depth: 2, base: 0 },
        close_column: 0,
    };
    for head in ["> > F [e]", "> > F [e] @"] {
        let source = format!("{head}\r\n> > ```\nouter");
        let (green, exit, remainder) =
            run_type_normalized(&source, 41, LineEntry::PhysicalStart, Some(&fence));
        assert_eq!(green.to_string(), head);
        let Some(NormalizedExit::Complete(Err(Either::Left(pending)), LineEntry::PhysicalStart)) =
            exit
        else {
            panic!("fence")
        };
        let coordinate = 41 + head.len() + 2;
        assert_eq!(
            pending
                .payload_view()
                .pending_boundary()
                .unwrap()
                .coordinate(),
            coordinate
        );
        assert_eq!(
            pending.extent(coordinate).recovery_range(),
            41 + head.len()..coordinate
        );
        let mut output = GreenNodeBuilder::new();
        output.start_node(SyntaxKind::Root.into());
        pending.emit_terminal_boundary(&mut output);
        output.finish_node();
        assert_eq!(output.finish().to_string(), "\r\n");
        assert_eq!(format!("{head}\r\n{remainder}"), source);
        let root = SyntaxNode::new_root(green);
        let expected = if head.ends_with('@') {
            vec![
                (SyntaxKind::BracketRow, "[e]".into()),
                (SyntaxKind::Whitespace, " ".into()),
                (SyntaxKind::Error, "@".into()),
            ]
        } else {
            vec![
                (SyntaxKind::BracketRow, "[e]".into()),
                (SyntaxKind::Missing, "".into()),
            ]
        };
        assert_eq!(children(&tail(&root)), expected);
    }
}

#[test]
fn bracket_arrow_cst_public_root_conserves_recovery_and_eof_trivia() {
    use crate::{SourceText, SyntaxEnvironment, parse_file, scan_header};
    for source in [
        "type T = F [e] @/*é*/: U",
        "type T = F [e] @ \r\n",
        "type T = F [A",
        "type T = F [e] @ ->",
    ] {
        let source: Arc<SourceText> = Arc::from(source);
        let parsed = parse_file(
            Arc::clone(&source),
            Arc::new(scan_header(Arc::clone(&source))),
            Arc::new(SyntaxEnvironment::empty()),
        );
        assert_eq!(parsed.green().to_string(), source.as_ref());
        let root = SyntaxNode::new_root(parsed.green().clone());
        assert_eq!(children(&tail(&root))[0].0, SyntaxKind::BracketRow);
    }
}
