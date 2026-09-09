//! Direct Rowan evidence for the required primary after a leading BracketRow.
use super::*;

fn children(node: &SyntaxNode) -> Vec<(SyntaxKind, String)> {
    node.children_with_tokens()
        .map(|child| (child.kind(), child.to_string()))
        .collect()
}

fn head(source: &str) -> SyntaxNode {
    let (green, _) = run_type(source);
    top_type_expression(&green)
}

#[test]
fn leading_head_cst_admits_direct_primaries_and_their_existing_continuations() {
    for (text, kind) in [
        ("T", SyntaxKind::Identifier),
        ("'a", SyntaxKind::SigilIdentifier),
        ("42", SyntaxKind::Integer),
        ("(A)", SyntaxKind::ParenthesizedTypeGroup),
        ("{a: A}", SyntaxKind::NamedRecordType),
        (":{A}", SyntaxKind::PolymorphicVariantType),
        ("'[io]", SyntaxKind::EffectRowType),
        ("for 'a: T", SyntaxKind::ForallType),
    ] {
        let source = format!("[e] {text}");
        let owner = head(&source);
        assert_eq!(
            children(&owner),
            [
                (SyntaxKind::BracketRow, "[e]".into()),
                (SyntaxKind::Whitespace, " ".into()),
                (kind, text.into()),
            ],
            "{source}"
        );
    }
    let owner = head("[e] F [io] -> U");
    let tail = owner
        .children()
        .find(|n| n.kind() == SyntaxKind::TypeArrowTail)
        .unwrap();
    assert_eq!(tail.parent(), Some(owner.clone()));
    assert_eq!(tail.to_string(), "[io] -> U");
    assert!(
        !owner
            .children()
            .any(|n| n.kind() == SyntaxKind::TypeExpression)
    );
}

#[test]
fn leading_head_cst_missing_and_incomplete_row_have_distinct_parents() {
    for (source, row, at, leading) in [
        ("[e]", "[e]", 3, ""),
        ("[e] ", "[e]", 4, " "),
        ("[e", "[e", 2, ""),
    ] {
        let owner = head(source);
        let mut expected = vec![(SyntaxKind::BracketRow, row.into())];
        if !leading.is_empty() {
            expected.push((SyntaxKind::Whitespace, leading.into()));
        }
        expected.push((SyntaxKind::Missing, "".into()));
        assert_eq!(children(&owner), expected);
        let missing = owner.children().last().unwrap();
        assert_eq!(usize::from(missing.text_range().start()), at);
        assert!(missing.text_range().is_empty());
        if source == "[e" {
            let row = owner.children().next().unwrap();
            let close = row
                .children()
                .find(|n| n.kind() == SyntaxKind::Missing)
                .unwrap();
            assert_eq!(close.text_range(), missing.text_range());
            assert_ne!(close.parent(), missing.parent());
        }
    }
}

#[test]
fn leading_head_cst_terminal_primaries_keep_continuations_inside_their_owner() {
    let owner = head("[e] for 'a: A -> B");
    assert_eq!(
        children(&owner),
        [
            (SyntaxKind::BracketRow, "[e]".into()),
            (SyntaxKind::Whitespace, " ".into()),
            (SyntaxKind::ForallType, "for 'a: A -> B".into()),
        ]
    );
    let forall = owner.children().last().unwrap();
    let arrow = forall
        .descendants()
        .find(|n| n.kind() == SyntaxKind::TypeArrowTail)
        .unwrap();
    let body = arrow.parent().unwrap();
    assert_eq!(body.kind(), SyntaxKind::TypeExpression);
    assert!(body.ancestors().any(|n| n == forall));
    assert_eq!(arrow.to_string(), " -> B");

    for (suffix, stops) in [
        ("\n B", 0),
        ("\r\n B", 0),
        (" with tail", crate::lexical::stops::STOP_WITH),
    ] {
        let prefix = "[e] :{A Int";
        let source = format!("{prefix}{suffix}");
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
        let owner = top_type_expression(&run.green);
        assert_eq!(
            children(&owner),
            [
                (SyntaxKind::BracketRow, "[e]".into()),
                (SyntaxKind::Whitespace, " ".into()),
                (SyntaxKind::PolymorphicVariantType, ":{A Int".into()),
            ]
        );
        let variant = owner.children().last().unwrap();
        assert!(variant.children().any(|n| n.kind() == SyntaxKind::Missing));
        let NormalizedExit::Complete(Err(Either::Left(pending)), line) = run.exit else {
            panic!("terminal variant boundary")
        };
        let (control, origin, control_line, remainder, _, _) =
            scan_type_item_control(suffix, prefix.len(), &OperatorTable::empty());
        assert_eq!(pending, control);
        assert_eq!(run.successor_origin, origin);
        assert_eq!(line, control_line);
        assert_eq!(run.remainder, remainder);
    }
}

#[test]
fn incomplete_variant_cst_keeps_boundary_on_direct_and_recovered_head_routes() {
    for head_prefix in ["", "[e] ", "[e] @ "] {
        for (suffix, stops, outer_closes) in [
            ("\n B tail", 0, 0),
            ("\r\n B tail", 0, 0),
            (" with tail", crate::lexical::stops::STOP_WITH, 0),
            (" ; tail", crate::lexical::stops::STOP_SEMICOLON, 0),
            (
                " ) tail",
                0,
                crate::type_expr::with_type_outer_close(0, TokenKind::RParen),
            ),
        ] {
            let prefix = format!("{head_prefix}:{{A Int");
            let source = format!("{prefix}{suffix}");
            let run = run_contextual_type_snapshot(
                &source,
                crate::type_expr::TypeMlContext::INACTIVE,
                stops,
                outer_closes,
                0,
                LineEntry::InLine,
                None,
                None,
            );
            assert_eq!(run.green.to_string(), format!("sentinel{prefix}"));
            let owner = top_type_expression(&run.green);
            let variant = owner.children().last().unwrap();
            assert_eq!(variant.kind(), SyntaxKind::PolymorphicVariantType);
            assert_eq!(variant.to_string(), ":{A Int");
            assert_eq!(
                variant.children().last().unwrap().kind(),
                SyntaxKind::Missing
            );
            let NormalizedExit::Complete(Err(Either::Left(pending)), line) = run.exit else {
                panic!("incomplete variant must return its boundary: {source}")
            };
            let (control, origin, control_line, remainder, _, _) =
                scan_type_item_control(suffix, prefix.len(), &OperatorTable::empty());
            assert_eq!(pending, control);
            assert_eq!(run.successor_origin, origin);
            assert_eq!(line, control_line);
            assert_eq!(run.remainder, remainder);
        }
        let source = format!("{head_prefix}:{{A Int");
        let run = run_contextual_type_snapshot(
            &source,
            crate::type_expr::TypeMlContext::INACTIVE,
            0,
            0,
            0,
            LineEntry::InLine,
            None,
            None,
        );
        assert_eq!(run.green.to_string(), format!("sentinel{source}"));
        assert!(matches!(
            run.exit,
            NormalizedExit::Complete(Err(Either::Right(_)), LineEntry::InLine)
        ));
        assert_eq!(run.successor_origin, source.len());
        assert_eq!(run.remainder, "");

        let source = format!("{head_prefix}:{{A Int}} -> U");
        let owner = head(&source);
        assert_eq!(owner.to_string(), source);
        assert_eq!(
            owner.children().last().unwrap().kind(),
            SyntaxKind::TypeArrowTail
        );
        assert!(!owner.descendants().any(|n| n.kind() == SyntaxKind::Missing));
    }
}

#[test]
fn incomplete_variant_cst_preserves_quoted_fence_after_each_head_route() {
    let fence = FenceBoundary {
        opener: FenceOpener {
            line: 0,
            marker: 0..3,
            marker_width: 3,
        },
        prefix_policy: FencePrefixPolicy::ActivePrefixQuote { depth: 2, base: 0 },
        close_column: 0,
    };
    for head_prefix in ["", "[e] ", "[e] @ "] {
        for newline in ["\n", "\r\n"] {
            let prefix = format!("> > {head_prefix}:{{A Int");
            let source = format!("{prefix}{newline}> > ```\nouter");
            let run = run_contextual_type_snapshot(
                &source,
                crate::type_expr::TypeMlContext::INACTIVE,
                0,
                0,
                0,
                LineEntry::PhysicalStart,
                Some(&fence),
                None,
            );
            assert_eq!(run.green.to_string(), format!("sentinel{prefix}"));
            let variant = top_type_expression(&run.green).children().last().unwrap();
            assert_eq!(variant.kind(), SyntaxKind::PolymorphicVariantType);
            assert_eq!(
                variant.children().last().unwrap().kind(),
                SyntaxKind::Missing
            );
            let NormalizedExit::Complete(Err(Either::Left(pending)), LineEntry::PhysicalStart) =
                run.exit
            else {
                panic!("incomplete PV fence")
            };
            let coordinate = prefix.len() + newline.len();
            assert_eq!(
                pending
                    .payload_view()
                    .pending_boundary()
                    .unwrap()
                    .coordinate(),
                coordinate
            );
            assert_eq!(run.successor_origin, coordinate);
            assert_eq!(run.remainder, "> > ```\nouter");
            let mut output = GreenNodeBuilder::new();
            output.start_node(SyntaxKind::Root.into());
            pending.emit_terminal_boundary(&mut output);
            output.finish_node();
            assert_eq!(output.finish().to_string(), newline);
        }
    }
}

#[test]
fn leading_head_cst_error_fragments_keep_leading_and_retry_outside_the_run() {
    for (source, initial, run, suffix) in [
        ("[e][f]T", "", "[f]", "T"),
        ("[e][/*é*/f(A,{x})]T", "", "[/*é*/f(A,{x})]", "T"),
        ("[e][[a],b;[c]]T", "", "[[a],b;[c]]", "T"),
        ("[e] @ [f] T", " ", "@ [f]", " T"),
        ("[e] @ : T", " ", "@ :", " T"),
        ("[e] @/*é*/T", " ", "@", "/*é*/T"),
        ("[e][f", "", "[f", ""),
        ("[e][f ", "", "[f", " "),
        ("[e] @ ", " ", "@", " "),
    ] {
        let owner = head(source);
        assert_eq!(owner.to_string(), source);
        let direct = owner.children_with_tokens().collect::<Vec<_>>();
        let first = direct
            .iter()
            .position(|c| c.kind() == SyntaxKind::Error)
            .unwrap();
        assert_eq!(
            direct[1..first]
                .iter()
                .map(ToString::to_string)
                .collect::<String>(),
            initial
        );
        let errors = direct[first..]
            .iter()
            .take_while(|c| c.kind() == SyntaxKind::Error)
            .collect::<Vec<_>>();
        assert!(errors.iter().all(|c| c.as_token().is_some()));
        assert_eq!(
            errors.iter().map(|c| c.to_string()).collect::<String>(),
            run
        );
        assert_eq!(
            usize::from(errors[0].text_range().start()),
            3 + initial.len()
        );
        assert_eq!(
            usize::from(errors.last().unwrap().text_range().end()),
            3 + initial.len() + run.len()
        );
        assert_eq!(
            direct[first + errors.len()..]
                .iter()
                .map(ToString::to_string)
                .collect::<String>(),
            suffix
        );
        assert_eq!(
            owner
                .children()
                .filter(|n| n.kind() == SyntaxKind::BracketRow)
                .count(),
            1
        );
        assert!(
            !owner
                .children()
                .any(|n| n.kind() == SyntaxKind::TypeExpression)
        );
        assert!(
            !owner
                .descendants()
                .any(|n| matches!(n.kind(), SyntaxKind::Missing | SyntaxKind::Invalid))
        );
    }
}

#[test]
fn leading_head_cst_protected_items_remain_whole_at_each_recovery_depth() {
    for prefix in ["[e]", "[e] @", "[e][bad", "[e][f(bad"] {
        for (suffix, stops) in [
            (" with tail", crate::lexical::stops::STOP_WITH),
            (" /*é*/else tail", crate::lexical::stops::STOP_ELSE),
            (" , tail", crate::lexical::stops::STOP_COMMA),
            (" ; tail", crate::lexical::stops::STOP_SEMICOLON),
            (" } tail", 0),
        ] {
            let source = format!("{prefix}{suffix}");
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
            assert_eq!(run.green.to_string(), format!("sentinel{prefix}"));
            let owner = top_type_expression(&run.green);
            assert_eq!(
                owner
                    .children()
                    .filter(|n| n.kind() == SyntaxKind::Missing)
                    .count(),
                usize::from(prefix == "[e]")
            );
            let NormalizedExit::Complete(Err(Either::Left(pending)), line) = run.exit else {
                panic!("pending {source}")
            };
            let (control, origin, control_line, remainder, _, _) =
                scan_type_item_control(suffix, prefix.len(), &OperatorTable::empty());
            assert_eq!(pending, control);
            assert_eq!(run.successor_origin, origin);
            assert_eq!(line, control_line);
            assert_eq!(run.remainder, remainder);
        }
    }
    for prefix in ["[e]", "[e][bad"] {
        let source = format!("{prefix} with tail");
        let (green, exit, accepted, origin, remainder, _, _, _) =
            run_required_type_with_outer_boundary_and_recoveries(
                &source,
                crate::type_expr::TypeOuterBoundary::WITH,
                false,
                None,
            );
        assert!(accepted);
        assert_eq!(green.to_string(), prefix);
        let NormalizedExit::Complete(Err(Either::Left(pending)), _) = exit else {
            panic!("outer WITH")
        };
        let (control, control_origin, _, control_remainder, _, _) =
            scan_type_item_control(" with tail", prefix.len(), &OperatorTable::empty());
        assert_eq!(pending, control);
        assert_eq!(origin, control_origin);
        assert_eq!(remainder, control_remainder);
    }
}

#[test]
fn leading_head_cst_layout_protects_shallow_and_equal_items_and_admits_deeper_heads() {
    for newline in ["\n", "\r\n"] {
        for indent in [" ", "  ", "   "] {
            for prefix in ["[e]", "[e] @", "[e][bad"] {
                let source = format!("{prefix}{newline}{indent}T");
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
                    crate::cursor::SyntaxIn::new(&mut input, &mut recover, &mut output),
                    primary, 2, 0, crate::type_expr::TypeOuterBoundary::NONE, origin, line, None);
                assert!(accepted);
                output.finish_node();
                let owner = top_type_expression(&finish_with_discarded_recoveries(output, recover));
                if indent.len() > 2 {
                    assert_eq!(owner.to_string(), source);
                    assert!(!owner.children().any(|n| n.kind() == SyntaxKind::Missing));
                    assert_eq!(owner.last_token().unwrap().text(), "T");
                    assert_eq!(
                        owner.last_token().unwrap().kind(),
                        if prefix == "[e][bad" {
                            SyntaxKind::Error
                        } else {
                            SyntaxKind::Identifier
                        }
                    );
                } else {
                    assert_eq!(owner.to_string(), prefix);
                    assert_eq!(
                        owner
                            .children()
                            .filter(|n| n.kind() == SyntaxKind::Missing)
                            .count(),
                        usize::from(prefix == "[e]")
                    );
                    let NormalizedExit::Complete(Err(Either::Left(pending)), _) = exit else {
                        panic!("shallow head")
                    };
                    let (control, _, _, _, _, _) = scan_type_item_control(
                        &source[prefix.len()..],
                        prefix.len(),
                        &OperatorTable::empty(),
                    );
                    assert_eq!(pending, control);
                }
            }
        }
    }
}

#[test]
fn leading_head_cst_fence_missing_uses_rowan_range_before_pending_coordinate() {
    let fence = FenceBoundary {
        opener: FenceOpener {
            line: 0,
            marker: 0..3,
            marker_width: 3,
        },
        prefix_policy: FencePrefixPolicy::ActivePrefixQuote { depth: 2, base: 0 },
        close_column: 0,
    };
    for prefix in ["> > [e]", "> > [e] @", "> > [e] [bad"] {
        for leading in ["\n", "\r\n", "/*\n> > still\n"] {
            let source = format!("{prefix}{leading}> > ```\nouter]");
            let (green, exit, remainder) =
                run_type_normalized(&source, 0, LineEntry::PhysicalStart, Some(&fence));
            assert_eq!(green.to_string(), prefix);
            let owner = top_type_expression(&green);
            let missing = owner.children().find(|n| n.kind() == SyntaxKind::Missing);
            assert_eq!(missing.is_some(), prefix == "> > [e]");
            if let Some(missing) = missing {
                assert_eq!(usize::from(missing.text_range().start()), prefix.len());
                assert!(missing.text_range().is_empty());
            }
            let errors = owner
                .children_with_tokens()
                .filter(|child| child.kind() == SyntaxKind::Error)
                .collect::<Vec<_>>();
            if prefix == "> > [e]" {
                assert!(errors.is_empty());
            } else {
                assert!(errors.iter().all(|child| child.as_token().is_some()));
                assert_eq!(usize::from(errors.first().unwrap().text_range().start()), 8);
                assert_eq!(
                    usize::from(errors.last().unwrap().text_range().end()),
                    if prefix == "> > [e] @" { 9 } else { 12 }
                );
                assert_eq!(
                    errors.iter().map(ToString::to_string).collect::<String>(),
                    if prefix == "> > [e] @" { "@" } else { "[bad" }
                );
            }
            let Some(NormalizedExit::Complete(
                Err(Either::Left(pending)),
                LineEntry::PhysicalStart,
            )) = exit
            else {
                panic!("fence")
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
            assert_eq!(output.finish().to_string(), leading);
            assert_eq!(format!("{prefix}{leading}{remainder}"), source);
        }
    }
}

#[test]
fn leading_head_cst_outer_invalid_retains_nested_slot_and_public_root_conserves_source() {
    for source in [":{[e]}", ":{[e][f]T}"] {
        let owner = head(source);
        let invalid = owner
            .descendants()
            .find(|n| n.kind() == SyntaxKind::Invalid)
            .unwrap();
        let nested = invalid
            .descendants()
            .find(|n| n.kind() == SyntaxKind::TypeExpression)
            .unwrap();
        assert_eq!(
            nested.children().next().unwrap().kind(),
            SyntaxKind::BracketRow
        );
        assert_eq!(
            nested.children().any(|n| n.kind() == SyntaxKind::Missing),
            source == ":{[e]}"
        );
        assert_eq!(
            nested
                .children_with_tokens()
                .any(|n| n.kind() == SyntaxKind::Error),
            source == ":{[e][f]T}"
        );
    }
    for text in [
        "type T = [e] @  ",
        "type T = [e][/*é*/f]T\r\n",
        "type T = [e] ",
    ] {
        let source: Arc<crate::SourceText> = Arc::from(text);
        let parsed = crate::parse_file(
            Arc::clone(&source),
            Arc::new(crate::scan_header(Arc::clone(&source))),
            Arc::new(crate::SyntaxEnvironment::empty()),
        );
        assert_eq!(parsed.green().to_string(), text);
        let root = SyntaxNode::new_root(parsed.green().clone());
        assert!(
            root.descendants()
                .any(|n| n.kind() == SyntaxKind::BracketRow)
        );
    }
}
