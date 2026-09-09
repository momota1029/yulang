//! Direct Rowan evidence for the suffix beginning at an actual Arrow token.
use super::*;

#[test]
fn actual_arrow_rhs_cst_public_root_preserves_raw_error_and_eof_leading() {
    use crate::{SourceText, SyntaxEnvironment, parse_file, scan_header};
    let source: Arc<SourceText> = Arc::from("type T = A-> @/*é*/.  ");
    let parsed = parse_file(
        Arc::clone(&source),
        Arc::new(scan_header(Arc::clone(&source))),
        Arc::new(SyntaxEnvironment::empty()),
    );
    assert_eq!(parsed.green().to_string(), source.as_ref());
    let root = SyntaxNode::new_root(parsed.green().clone());
    let owner = tail(&root);
    assert_eq!(owner.to_string(), "-> @/*é*/.");
    assert_eq!(owner.last_token().unwrap().kind(), SyntaxKind::Error);
    let eof = root.last_token().unwrap();
    assert_eq!((eof.kind(), eof.text()), (SyntaxKind::Whitespace, "  "));
    assert!(!eof.parent_ancestors().any(|node| node == owner));
}

fn tail(root: &SyntaxNode) -> SyntaxNode {
    root.descendants()
        .find(|node| node.kind() == SyntaxKind::TypeArrowTail)
        .expect("TypeArrowTail")
}

fn boundary_leading(item: Item) -> String {
    let mut output = GreenNodeBuilder::new();
    output.start_node(SyntaxKind::Root.into());
    item.emit_terminal_boundary(&mut output);
    output.finish_node();
    output.finish().to_string()
}

fn children(node: &SyntaxNode) -> Vec<(SyntaxKind, String)> {
    node.children_with_tokens()
        .map(|child| (child.kind(), child.to_string()))
        .collect()
}

#[test]
fn actual_arrow_rhs_cst_caller_close_and_separator_keep_exact_pending_item() {
    for (punctuation, kind) in [(")", TokenKind::RParen), (",", TokenKind::Comma)] {
        for malformed in [false, true] {
            let head = if malformed { "A->@" } else { "A->" };
            let source = format!("{head} {punctuation} rest");
            let operators = OperatorTable::empty();
            let mut input = source.as_str();
            let mut recover = Recover::new_for_test(&operators);
            let mut output = GreenNodeBuilder::new();
            output.start_node(SyntaxKind::Root.into());
            let (exit, origin) = crate::type_expr::type_expr_with_caller_stops_for_test(
                crate::cursor::SyntaxIn::new(&mut input, &mut recover, &mut output),
                crate::lexical::stops::stops_for(TokenKind::RParen),
                0,
                0,
            )
            .unwrap();
            output.finish_node();
            let root = SyntaxNode::new_root(finish_with_discarded_recoveries(output, recover));
            let NormalizedExit::Complete(Err(Either::Left(mut pending)), line) = exit else {
                panic!("pending punctuation")
            };
            let (mut control, control_origin, control_line, control_remainder, _, _) =
                scan_type_item_control(&source[head.len()..], head.len(), &operators);
            if !malformed {
                assert_eq!(emit_pending_leading_text(&mut control), " ");
            }
            assert_eq!(pending, control);
            assert_eq!(pending.payload_view().token_kind(), Some(kind));
            assert_eq!(origin, control_origin);
            assert_eq!(line, control_line);
            assert_eq!(input, control_remainder);
            assert_eq!(input, " rest");
            let leading = emit_pending_leading_text(&mut pending);
            assert_eq!(leading, if malformed { " " } else { "" });
            assert_eq!(format!("{}{leading}{punctuation}{input}", root), source);
            let mut expected = vec![(SyntaxKind::Arrow, "->".into())];
            if !malformed {
                expected.push((SyntaxKind::Whitespace, " ".into()));
            }
            expected.push((
                if malformed {
                    SyntaxKind::Error
                } else {
                    SyntaxKind::Missing
                },
                if malformed { "@".into() } else { "".into() },
            ));
            assert_eq!(children(&tail(&root)), expected);
        }
    }
}

#[test]
fn actual_arrow_rhs_cst_nonzero_origin_and_foreign_prefix_preserve_positions() {
    let fence = FenceBoundary {
        opener: FenceOpener {
            line: 0,
            marker: 0..3,
            marker_width: 3,
        },
        prefix_policy: FencePrefixPolicy::ActivePrefixQuote { depth: 2, base: 0 },
        close_column: 0,
    };
    let source = "> > A->@\r\n> >   B\r\n> > ```\nouter\n";
    let base = 41;
    let emitted = "> > A->@\r\n> >   B";
    let (green, exit, remainder) =
        run_type_normalized(source, base, LineEntry::PhysicalStart, Some(&fence));
    assert_eq!(green.to_string(), emitted);
    let Some(NormalizedExit::Complete(Err(Either::Left(pending)), LineEntry::PhysicalStart)) = exit
    else {
        panic!("pending quoted fence")
    };
    let coordinate = base + emitted.len() + 2;
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
        base + emitted.len()..coordinate
    );
    assert_eq!(boundary_leading(pending), "\r\n");
    assert_eq!(format!("{emitted}\r\n{remainder}"), source);
    let root = SyntaxNode::new_root(green);
    let owner = tail(&root);
    assert_eq!(
        children(&owner),
        [
            (SyntaxKind::Arrow, "->".into()),
            (SyntaxKind::Error, "@".into()),
            (SyntaxKind::TypeExpression, "\r\n> >   B".into())
        ]
    );
    let error = owner
        .children_with_tokens()
        .find(|child| child.kind() == SyntaxKind::Error)
        .unwrap();
    assert_eq!(usize::from(error.text_range().start()), 7);
    assert_eq!(usize::from(error.text_range().end()), 8);
    let rhs = owner.children().next().unwrap();
    assert_eq!(
        rhs.descendants_with_tokens()
            .filter(|child| child.kind() == SyntaxKind::YmQuotePrefix)
            .map(|child| child.to_string())
            .collect::<String>(),
        "> > "
    );
}

#[test]
fn actual_arrow_rhs_cst_orders_leading_and_right_associative_children() {
    let (green, _) = run_type("A -> B -> C");
    let root = SyntaxNode::new_root(green);
    let outer = tail(&root);
    assert_eq!(
        children(&outer),
        [
            (SyntaxKind::Whitespace, " ".into()),
            (SyntaxKind::Arrow, "->".into()),
            (SyntaxKind::TypeExpression, " B -> C".into()),
        ]
    );
    let rhs = outer.children().next().unwrap();
    let inner = tail(&rhs);
    assert_eq!(inner.parent(), Some(rhs));
    assert_eq!(
        children(&inner),
        [
            (SyntaxKind::Whitespace, " ".into()),
            (SyntaxKind::Arrow, "->".into()),
            (SyntaxKind::TypeExpression, " C".into()),
        ]
    );
}

#[test]
fn actual_arrow_rhs_cst_missing_follows_owned_native_leading() {
    for (source, leading, at) in [("A->", "", 3), ("A-> ", " ", 4), ("A-> )", " ", 4)] {
        let (green, _) = run_type(source);
        let root = SyntaxNode::new_root(green);
        let owner = tail(&root);
        let mut expected = vec![(SyntaxKind::Arrow, "->".into())];
        if !leading.is_empty() {
            expected.push((SyntaxKind::Whitespace, leading.into()));
        }
        expected.push((SyntaxKind::Missing, "".into()));
        assert_eq!(children(&owner), expected, "{source:?}");
        let missing = owner.children().last().unwrap();
        assert_eq!(usize::from(missing.text_range().start()), at);
        assert!(missing.text_range().is_empty());
    }
}

#[test]
fn actual_arrow_rhs_cst_raw_runs_and_retry_have_separate_leading_owners() {
    for (source, run, retry) in [
        ("A-> @ . B", " @ .", Some(" B")),
        ("A-> @/*é*/. B", " @/*é*/.", Some(" B")),
        ("A-> @ .", " @ .", None),
        ("A-> @ . )", " @ .", None),
    ] {
        let (green, _) = run_type(source);
        let root = SyntaxNode::new_root(green);
        let owner = tail(&root);
        let direct = owner.children_with_tokens().collect::<Vec<_>>();
        assert_eq!(direct[0].kind(), SyntaxKind::Arrow);
        let errors = direct
            .iter()
            .skip(1)
            .take_while(|child| child.kind() == SyntaxKind::Error)
            .collect::<Vec<_>>();
        assert!(!errors.is_empty());
        assert!(errors.iter().all(|child| child.as_token().is_some()));
        assert_eq!(
            errors
                .iter()
                .map(|child| child.to_string())
                .collect::<String>(),
            run,
            "{source:?}"
        );
        let suffix = &direct[1 + errors.len()..];
        if let Some(text) = retry {
            assert_eq!(suffix.len(), 1);
            assert_eq!(suffix[0].kind(), SyntaxKind::TypeExpression);
            assert_eq!(suffix[0].to_string(), text);
        } else {
            assert!(suffix.is_empty(), "{source:?}");
        }
        assert!(
            !owner
                .descendants()
                .any(|node| matches!(node.kind(), SyntaxKind::Missing | SyntaxKind::Invalid))
        );
    }
}

#[test]
fn actual_arrow_rhs_cst_distinguishes_bracket_required_arrow_and_nested_rhs_missing() {
    for (source, actual_arrow) in [("F [e]", false), ("F [e] ->", true)] {
        let (green, _) = run_type(source);
        assert_eq!(green.to_string(), source);
        let root = SyntaxNode::new_root(green);
        let owner = tail(&root);
        let direct = children(&owner);
        let significant = direct
            .iter()
            .filter(|(kind, _)| *kind != SyntaxKind::Whitespace)
            .cloned()
            .collect::<Vec<_>>();
        let mut expected = vec![(SyntaxKind::BracketRow, "[e]".into())];
        if actual_arrow {
            expected.push((SyntaxKind::Arrow, "->".into()));
        }
        expected.push((SyntaxKind::Missing, String::new()));
        assert_eq!(significant, expected);
        assert_eq!(
            direct.iter().any(|(kind, _)| *kind == SyntaxKind::Arrow),
            actual_arrow
        );
        assert_eq!(direct.last(), Some(&(SyntaxKind::Missing, String::new())));
        assert_eq!(
            owner
                .children()
                .filter(|node| node.kind() == SyntaxKind::Missing)
                .count(),
            1
        );
    }
    let (green, _) = run_type("A-> B->");
    let root = SyntaxNode::new_root(green);
    let outer = tail(&root);
    assert_eq!(
        children(&outer),
        [
            (SyntaxKind::Arrow, "->".into()),
            (SyntaxKind::TypeExpression, " B->".into())
        ]
    );
    let missing = root
        .descendants()
        .find(|node| node.kind() == SyntaxKind::Missing)
        .unwrap();
    let rhs = outer.children().next().unwrap();
    let inner = tail(&rhs);
    assert_eq!(missing.parent(), Some(inner.clone()));
    assert_eq!(
        children(&inner),
        [
            (SyntaxKind::Arrow, "->".into()),
            (SyntaxKind::Missing, "".into())
        ]
    );
}

#[test]
fn actual_arrow_rhs_cst_outer_boundary_preserves_leading_before_and_after_error() {
    for (source, emitted, has_error) in [("A-> with", "A->", false), ("A->@ with", "A->@", true)] {
        let (green, exit, accepted, origin, remainder, _, _, _) =
            run_required_type_with_outer_boundary_and_recoveries(
                source,
                crate::type_expr::TypeOuterBoundary::WITH,
                false,
                None,
            );
        assert!(accepted);
        assert_eq!(green.to_string(), emitted);
        assert_eq!(remainder, "");
        let NormalizedExit::Complete(Err(Either::Left(mut pending)), _) = exit else {
            panic!("pending WITH")
        };
        assert_eq!(
            pending.extent(origin).recovery_range(),
            emitted.len()..source.len()
        );
        let operators = OperatorTable::empty();
        let (control, control_origin, _, control_remainder, _, _) =
            scan_type_item_control(&source[emitted.len()..], emitted.len(), &operators);
        assert_eq!(pending, control);
        assert_eq!(origin, control_origin);
        assert_eq!(remainder, control_remainder);
        assert_eq!(format!("{emitted}{}", &source[emitted.len()..]), source);
        assert_eq!(emit_pending_leading_text(&mut pending), " ");
        let root = SyntaxNode::new_root(green);
        assert_eq!(
            children(&tail(&root)),
            [
                (SyntaxKind::Arrow, "->".into()),
                (
                    if has_error {
                        SyntaxKind::Error
                    } else {
                        SyntaxKind::Missing
                    },
                    if has_error { "@".into() } else { "".into() }
                ),
            ]
        );
    }
}

#[test]
fn actual_arrow_rhs_cst_layout_distinguishes_initial_missing_and_post_error_exit() {
    for newline in ["\n", "\r\n"] {
        for indent in [" ", "  ", "   "] {
            for malformed in [false, true] {
                let head = if malformed { "A->@" } else { "A->" };
                let source = format!("{head}{newline}{indent}B");
                let operators = OperatorTable::empty();
                let mut input = source.as_str();
                let mut recover = Recover::new_for_test(&operators);
                let mut output = GreenNodeBuilder::new();
                output.start_node(SyntaxKind::Root.into());
                let (primary, origin, line) = crate::type_expr::type_nud_item_normalized(
                    crate::cursor::SyntaxIn::new(&mut input, &mut recover, &mut output),
                    0,
                    LineEntry::InLine,
                    None,
                );
                let (exit, accepted) = crate::type_expr::required_type_expr_with_caller_stops_and_outer_boundary_normalized(
                    crate::cursor::SyntaxIn::new(&mut input, &mut recover, &mut output), primary, 2, 0,
                    crate::type_expr::TypeOuterBoundary::NONE, origin, line, None);
                assert!(accepted);
                output.finish_node();
                let root = SyntaxNode::new_root(finish_with_discarded_recoveries(output, recover));
                let owner = tail(&root);
                let rhs = owner
                    .children()
                    .find(|node| node.kind() == SyntaxKind::TypeExpression);
                if indent.len() > 2 {
                    assert_eq!(rhs.unwrap().to_string(), format!("{newline}{indent}B"));
                    assert_eq!(root.to_string(), source);
                } else {
                    assert!(rhs.is_none());
                    let NormalizedExit::Complete(Err(Either::Left(mut pending)), _) = exit else {
                        panic!("pending shallow B")
                    };
                    let leading = emit_pending_leading_text(&mut pending);
                    if malformed {
                        assert_eq!(root.to_string(), head);
                        assert_eq!(leading, format!("{newline}{indent}"));
                        assert_eq!(
                            children(&owner),
                            [
                                (SyntaxKind::Arrow, "->".into()),
                                (SyntaxKind::Error, "@".into())
                            ]
                        );
                    } else {
                        assert_eq!(root.to_string(), format!("{head}{newline}{indent}"));
                        assert_eq!(leading, "");
                        assert_eq!(
                            children(&owner).last(),
                            Some(&(SyntaxKind::Missing, String::new()))
                        );
                    }
                }
            }
        }
    }
}

#[test]
fn actual_arrow_rhs_cst_quoted_fence_keeps_boundary_leading_and_has_no_error_cascade() {
    let fence = FenceBoundary {
        opener: FenceOpener {
            line: 0,
            marker: 0..3,
            marker_width: 3,
        },
        prefix_policy: FencePrefixPolicy::ActivePrefixQuote { depth: 2, base: 0 },
        close_column: 0,
    };
    for malformed in [false, true] {
        let head = if malformed { "> > A ->@" } else { "> > A ->" };
        let source = format!("{head}\n> > ```\nouter\n");
        let (green, exit, remainder) =
            run_type_normalized(&source, 0, LineEntry::PhysicalStart, Some(&fence));
        assert_eq!(green.to_string(), head);
        assert_eq!(remainder, "> > ```\nouter\n");
        let Some(NormalizedExit::Complete(Err(Either::Left(boundary)), LineEntry::PhysicalStart)) =
            exit
        else {
            panic!("pending fence")
        };
        assert!(boundary.payload_view().is_boundary());
        let coordinate = head.len() + 1;
        assert_eq!(
            boundary
                .payload_view()
                .pending_boundary()
                .unwrap()
                .coordinate(),
            coordinate
        );
        assert_eq!(
            boundary.extent(coordinate).recovery_range(),
            head.len()..coordinate
        );
        assert_eq!(boundary_leading(boundary), "\n");
        assert_eq!(format!("{head}\n{remainder}"), source);
        let root = SyntaxNode::new_root(green);
        assert_eq!(
            children(&tail(&root)),
            [
                (SyntaxKind::Whitespace, " ".into()),
                (SyntaxKind::Arrow, "->".into()),
                (
                    if malformed {
                        SyntaxKind::Error
                    } else {
                        SyntaxKind::Missing
                    },
                    if malformed { "@".into() } else { "".into() }
                ),
            ]
        );
    }
}
