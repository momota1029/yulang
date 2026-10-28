use crate::tests::type_expr::*;

pub(super) fn missing(_: u32, at: usize) -> ExpectedStructural {
    (StructuralKind::Missing, at..at)
}

#[allow(clippy::too_many_arguments)]
fn run_required<'source>(
    source: &'source str,
    origin: usize,
    line: LineEntry,
    fence: Option<&FenceBoundary>,
    emit_leading: bool,
) -> (ContextualTypeRun<'source>, bool) {
    let operators = OperatorTable::empty();
    let mut input = source;
    let mut recover = Recover::new_for_test(&operators);
    let mark = crate::cursor::LexRecover::new_for_test(recover.operators()).mark();
    let mut output = GreenNodeBuilder::new();
    output.start_node(SyntaxKind::Root.into());
    seed_identifier(&mut output);
    // A prior committed slot and CST sibling must survive this total attempt.
    output.start_node(SyntaxKind::Missing.into());
    output.finish_node();
    let (mut primary, next_origin, next_line) = crate::type_expr::type_nud_item_normalized(
        crate::cursor::SyntaxIn::new(&mut input, &mut recover, &mut output),
        origin,
        line,
        fence,
    );
    if emit_leading {
        primary.emit_all_remaining_leading(&mut output);
    }
    let (exit, found) = crate::type_expr::required_type_expr_with_caller_stops_and_outer_boundary_normalized_with_ambient(
        crate::cursor::SyntaxIn::new(&mut input, &mut recover, &mut output), primary, 0,
        crate::lexical::stops::STOP_WITH, crate::type_expr::TypeOuterBoundary::WITH,
        next_origin, next_line, fence,
        Some(crate::ambient_claim::AmbientClaimView::root_statement(0)).into());
    output.finish_node();
    let same_operators = std::ptr::eq(recover.operators(), &operators);
    let green = finish_with_discarded_recoveries(output, recover);
    let facts = structural_facts(&green);
    (
        ContextualTypeRun {
            green,
            exit,
            successor_origin: origin + source.len() - input.len(),
            remainder: input,
            facts,
            mark,
            same_operators,
        },
        found,
    )
}

pub(super) fn assert_same_exit(left: &NormalizedExit, right: &NormalizedExit) {
    match (left, right) {
        (
            NormalizedExit::Complete(Err(Either::Left(left)), line),
            NormalizedExit::Complete(Err(Either::Left(right)), right_line),
        ) => {
            assert_eq!(left, right);
            assert_eq!(line, right_line);
        }
        (
            NormalizedExit::Complete(Err(Either::Right(left)), line),
            NormalizedExit::Complete(Err(Either::Right(right)), right_line),
        ) => {
            assert_eq!(left, right);
            assert_eq!(line, right_line);
        }
        (NormalizedExit::Complete(Ok(()), line), NormalizedExit::Complete(Ok(()), right_line)) => {
            assert_eq!(line, right_line)
        }
        _ => panic!("complete exits must have the same variant"),
    }
}

#[test]
fn required_missing_preserves_remaining_extent_with_seeded_output() {
    for origin in [0, 41] {
        for (source, emit_leading, _at, emitted) in [
            ("", false, 0, ""),
            (" ", false, 0, ""),
            (" ", true, 1, " "),
            (" /*é*/ )tail", false, 0, ""),
            (" /*é*/ )tail", true, 8, " /*é*/ "),
            ("\n)tail", false, 0, ""),
            (" with tail", false, 0, ""),
        ] {
            let (fresh, found) =
                run_required(source, origin, LineEntry::InLine, None, emit_leading);
            assert!(!found);
            assert_eq!(fresh.green.to_string(), format!("sentinel{emitted}"));
            assert_eq!(fresh.mark, ());
            assert!(fresh.same_operators);
            let (mut control, next, line, remainder, _, _) =
                scan_type_item_control(source, origin, &OperatorTable::empty());
            if emit_leading {
                let mut leading_output = GreenNodeBuilder::new();
                leading_output.start_node(SyntaxKind::Root.into());
                control.emit_all_remaining_leading(&mut leading_output);
                leading_output.finish_node();
                assert_eq!(leading_output.finish().to_string(), emitted);
            }
            match &fresh.exit {
                NormalizedExit::Complete(Err(Either::Left(pending)), actual_line) => {
                    assert_eq!(pending, &control);
                    assert_eq!(*actual_line, line);
                }
                NormalizedExit::Complete(Err(Either::Right(end)), actual_line) => {
                    assert_eq!(end.item, control);
                    assert_eq!(*actual_line, line);
                }
                _ => panic!("required Missing must return its pending Item"),
            }
            assert_eq!(fresh.successor_origin, next);
            assert_eq!(fresh.remainder, remainder);
        }
    }
}

#[test]
fn required_missing_fence_uses_inspected_coordinate_without_absorbing_quoted_leading() {
    let fence = FenceBoundary {
        opener: FenceOpener {
            line: 0,
            marker: 0..3,
            marker_width: 3,
        },
        prefix_policy: FencePrefixPolicy::ActivePrefixQuote { depth: 2, base: 0 },
        close_column: 0,
    };
    let source = "> > \r\n> > ```\nouter";
    for origin in [0, 41] {
        let (fresh, found) = run_required(
            source,
            origin,
            LineEntry::PhysicalStart,
            Some(&fence),
            false,
        );
        assert!(!found);
        assert_eq!(fresh.green.to_string(), "sentinel");
        assert_eq!(fresh.remainder, "> > ```\nouter");
        assert_eq!(fresh.successor_origin, origin + 6);
        let NormalizedExit::Complete(Err(Either::Left(item)), LineEntry::PhysicalStart) =
            &fresh.exit
        else {
            panic!("quoted fence boundary remains pending")
        };
        assert_eq!(
            item.payload_view().pending_boundary().unwrap().coordinate(),
            origin + 6
        );
        assert!(item.leading_view().has_ordinary_newline());
    }
}

pub(super) fn run_statement_structural_facts<'source>(
    source: &'source str,
    origin: usize,
) -> ContextualTypeRun<'source> {
    let operators = OperatorTable::empty();
    let mut input = source;
    let mut recover = Recover::new_for_test(&operators);
    let mark = crate::cursor::LexRecover::new_for_test(recover.operators()).mark();
    let mut output = GreenNodeBuilder::new();
    output.start_node(SyntaxKind::Root.into());
    seed_identifier(&mut output);
    let mut exit = statement_normalized(
        crate::cursor::SyntaxIn::new(&mut input, &mut recover, &mut output),
        0,
        0,
        origin,
        LineEntry::InLine,
        None,
        Some(crate::ambient_claim::AmbientClaimView::root_statement(0)).into(),
        Some(crate::sequence::SequenceOwner::RootStatement),
    );
    if let NormalizedExit::Complete(Err(Either::Right(end)), _) = &mut exit {
        emit_end(&mut output, end);
    }
    output.finish_node();
    let same_operators = std::ptr::eq(recover.operators(), &operators);
    let green = finish_with_discarded_recoveries(output, recover);
    let facts = structural_facts(&green);
    ContextualTypeRun {
        green,
        exit,
        facts,
        successor_origin: origin + source.len() - input.len(),
        remainder: input,
        mark,
        same_operators,
    }
}

#[test]
fn required_type_real_declaration_callers_publish_their_own_missing_roles() {
    for origin in [0, 41] {
        for (source, at) in [
            ("type T =", 8),
            ("type T = ", 9),
            ("struct S {a:}", 12),
            ("struct S:\n  a:", 14),
            ("enum E { A from }", 16),
            ("error E { A from }", 17),
            ("enum E { A {a:} }", 14),
            ("error E { A {a:} }", 15),
            ("role ;", 5),
            ("impl ;", 5),
            ("impl T: ;", 8),
            ("act;", 3),
            ("act A = ;", 7),
            ("cast(x): ;", 9),
        ] {
            let expected = [missing(0, "sentinel".len() + at)];
            let fresh = run_statement_structural_facts(source, origin);
            assert_eq!(
                fresh.green.to_string(),
                format!("sentinel{source}"),
                "{source:?}"
            );
            assert_eq!(fresh.remainder, "", "{source:?}");
            assert_eq!(fresh.facts, expected, "{source:?}");
            assert_eq!(fresh.mark, ());
            assert!(fresh.same_operators);
            let root = SyntaxNode::new_root(fresh.green.clone());
            assert_eq!(
                root.descendants()
                    .filter(|node| node.kind() == SyntaxKind::Missing)
                    .count(),
                1,
                "{source:?}"
            );
            let replay = run_statement_structural_facts(source, origin);
            assert_eq!(replay.green, fresh.green);
            assert_eq!(replay.facts, fresh.facts);
            assert_same_exit(&fresh.exit, &replay.exit);
            assert_eq!(replay.successor_origin, fresh.successor_origin);
            assert_eq!(replay.remainder, fresh.remainder);
        }
    }
}

#[test]
fn named_field_required_type_missing_has_direct_three_owner_rowan_slots() {
    use SyntaxKind::{
        Colon, EnumDeclaration, EnumKw, EnumVariant, ErrorDeclaration, ErrorKw, Identifier, LBrace,
        Missing, RBrace, Root, Statement, StructDeclaration, StructField, StructKw, TypeExpression,
        Whitespace,
    };

    fn children(parent: &SyntaxNode, expected: &[(SyntaxKind, bool, Range<usize>, &str)]) {
        let actual = parent.children_with_tokens().collect::<Vec<_>>();
        assert_eq!(actual.len(), expected.len(), "{parent:#?}");
        for (child, (kind, node, range, text)) in actual.iter().zip(expected) {
            assert_eq!(child.parent().as_ref(), Some(parent));
            assert_eq!(child.kind(), *kind);
            assert_eq!(child.as_node().is_some(), *node);
            assert_eq!(child.as_token().is_some(), !node);
            assert_eq!(
                usize::from(child.text_range().start())..usize::from(child.text_range().end()),
                *range
            );
            assert_eq!(child.to_string(), *text);
        }
    }

    for (source, declaration_kind, keyword, keyword_end, field_start) in [
        ("struct S {a:}", StructDeclaration, StructKw, 6, 10),
        ("enum E { A {a:} }", EnumDeclaration, EnumKw, 4, 12),
        ("error E { A {a:} }", ErrorDeclaration, ErrorKw, 5, 13),
    ] {
        let (green, exit, remainder) = run_statement_normalized(source, 0, LineEntry::InLine, None);
        assert_eq!(green.to_string(), source);
        assert_eq!(remainder, "");
        let NormalizedExit::Complete(Err(Either::Right(mut end)), LineEntry::InLine) = exit else {
            panic!("{source:?}: expected EOF InLine");
        };
        assert!(end.item.payload_view().is_eof());
        assert_eq!(emit_pending_leading_text(&mut end.item), "");

        let root = SyntaxNode::new_root(green);
        assert_eq!(root.kind(), Root);
        assert_eq!(root.parent(), None);
        assert_eq!(
            root.text_range(),
            rowan::TextRange::new(0.into(), (source.len() as u32).into())
        );
        children(&root, &[(Statement, true, 0..source.len(), source)]);
        let statement = root.first_child().unwrap();
        children(
            &statement,
            &[(declaration_kind, true, 0..source.len(), source)],
        );
        let declaration = statement.first_child().unwrap();
        let mut shell = vec![
            (keyword, false, 0..keyword_end, &source[..keyword_end]),
            (Whitespace, false, keyword_end..keyword_end + 1, " "),
            (
                Identifier,
                false,
                keyword_end + 1..keyword_end + 2,
                &source[keyword_end + 1..keyword_end + 2],
            ),
            (Whitespace, false, keyword_end + 2..keyword_end + 3, " "),
            (LBrace, false, keyword_end + 3..keyword_end + 4, "{"),
        ];
        if declaration_kind == StructDeclaration {
            shell.push((StructField, true, field_start..field_start + 2, "a:"));
        } else {
            shell.push((
                EnumVariant,
                true,
                keyword_end + 4..field_start + 3,
                &source[keyword_end + 4..field_start + 3],
            ));
            shell.push((Whitespace, false, field_start + 3..field_start + 4, " "));
        }
        shell.push((RBrace, false, source.len() - 1..source.len(), "}"));
        children(&declaration, &shell);
        let field_owner = declaration.first_child().unwrap();
        let field = if field_owner.kind() == EnumVariant {
            children(
                &field_owner,
                &[
                    (Whitespace, false, keyword_end + 4..keyword_end + 5, " "),
                    (Identifier, false, keyword_end + 5..keyword_end + 6, "A"),
                    (Whitespace, false, keyword_end + 6..keyword_end + 7, " "),
                    (LBrace, false, keyword_end + 7..field_start, "{"),
                    (StructField, true, field_start..field_start + 2, "a:"),
                    (RBrace, false, field_start + 2..field_start + 3, "}"),
                ],
            );
            field_owner.first_child().unwrap()
        } else {
            field_owner
        };
        let at = field_start + 2;
        children(
            &field,
            &[
                (Identifier, false, field_start..field_start + 1, "a"),
                (Colon, false, field_start + 1..at, ":"),
                (TypeExpression, true, at..at, ""),
            ],
        );
        let type_expr = field.first_child().unwrap();
        children(&type_expr, &[(Missing, true, at..at, "")]);
        let missing_node = type_expr.first_child().unwrap();
        children(&missing_node, &[]);
        assert_eq!(
            root.descendants()
                .filter(|node| node.kind() == Missing)
                .count(),
            1
        );
        assert!(
            !root
                .descendants_with_tokens()
                .any(|element| matches!(element.kind(), SyntaxKind::Error | SyntaxKind::Invalid))
        );

        // Select the slot from the actual ordered CST before consulting records.
        let owner = field.parent().unwrap();
        let owner_children = owner.children_with_tokens().collect::<Vec<_>>();
        let field_index = owner_children
            .iter()
            .position(|child| child.as_node() == Some(&field))
            .unwrap();
        assert_eq!(owner_children[field_index - 1].kind(), LBrace);
        assert!(owner_children[field_index - 1].as_token().is_some());
        assert_eq!(owner_children[field_index + 1].kind(), RBrace);
        assert!(owner_children[field_index + 1].as_token().is_some());
        let ancestry = missing_node
            .ancestors()
            .map(|node| node.kind())
            .collect::<Vec<_>>();
        match ancestry.as_slice() {
            [
                Missing,
                TypeExpression,
                StructField,
                StructDeclaration,
                Statement,
                Root,
            ] => {}
            [
                Missing,
                TypeExpression,
                StructField,
                EnumVariant,
                EnumDeclaration,
                Statement,
                Root,
            ] => {}
            [
                Missing,
                TypeExpression,
                StructField,
                EnumVariant,
                ErrorDeclaration,
                Statement,
                Root,
            ] => {}
            _ => panic!("unexpected named-field ancestry: {ancestry:?}"),
        };
        let range = missing_node.text_range();
        assert!(range.is_empty());
        assert_eq!(usize::from(range.start())..usize::from(range.end()), at..at);
        let structural_projection = type_expr.children().collect::<Vec<_>>();
        assert_eq!(structural_projection, [missing_node.clone()]);
        assert!(missing_node.children_with_tokens().next().is_none());
        let expected = [missing(0, "sentinel".len() + usize::from(range.start()))];
        let mut fresh = run_statement_structural_facts(source, 0);
        let NormalizedExit::Complete(Err(Either::Right(end)), LineEntry::InLine) = &mut fresh.exit
        else {
            panic!("{source:?}: seeded harness must also return EOF InLine");
        };
        assert!(end.item.payload_view().is_eof());
        assert_eq!(emit_pending_leading_text(&mut end.item), "");
        assert_eq!(fresh.green.to_string(), format!("sentinel{source}"));
        let seeded_root = SyntaxNode::new_root(fresh.green.clone());
        let seeded_statement = seeded_root
            .children()
            .find(|node| node.kind() == Statement)
            .unwrap();
        assert_eq!(seeded_statement.green(), statement.green());
        assert_eq!(fresh.facts, expected);
        assert_eq!(fresh.mark, ());
        assert!(fresh.same_operators);
        assert_eq!(fresh.successor_origin, source.len());
        assert_eq!(fresh.remainder, "");
        let replay = run_statement_structural_facts(source, 0);
        assert_eq!(replay.green, fresh.green);
        assert_eq!(replay.facts, fresh.facts);
        assert_eq!(replay.mark, ());
        assert!(replay.same_operators);
        assert_same_exit(&fresh.exit, &replay.exit);
        assert_eq!(replay.successor_origin, fresh.successor_origin);
        assert_eq!(replay.remainder, fresh.remainder);
    }
}

#[test]
fn named_field_required_type_initial_error_has_direct_three_owner_rowan_slots() {
    use SyntaxKind::{
        Colon, EnumDeclaration, EnumKw, EnumVariant, Error, ErrorDeclaration, ErrorKw, Identifier,
        LBrace, RBrace, Root, Statement, StructDeclaration, StructField, StructKw, TypeExpression,
        Whitespace,
    };

    fn children(parent: &SyntaxNode, expected: &[(SyntaxKind, bool, Range<usize>, &str)]) {
        let actual = parent.children_with_tokens().collect::<Vec<_>>();
        assert_eq!(actual.len(), expected.len(), "{parent:#?}");
        for (child, (kind, node, range, text)) in actual.iter().zip(expected) {
            assert_eq!(child.parent().as_ref(), Some(parent));
            assert_eq!(child.kind(), *kind);
            assert_eq!(child.as_node().is_some(), *node);
            assert_eq!(child.as_token().is_some(), !node);
            assert_eq!(
                usize::from(child.text_range().start())..usize::from(child.text_range().end()),
                *range
            );
            assert_eq!(child.to_string(), *text);
        }
    }

    for (prefix, suffix, declaration_kind, keyword, keyword_end, f) in [
        ("struct S {a: ", "}", StructDeclaration, StructKw, 6, 10),
        ("enum E { A {a: ", "} }", EnumDeclaration, EnumKw, 4, 12),
        ("error E { A {a: ", "} }", ErrorDeclaration, ErrorKw, 5, 13),
    ] {
        for (rhs, retry, multileaf) in [
            ("@", false, false),
            ("@ T", true, false),
            ("@  ~   T", true, true),
        ] {
            let source = format!("{prefix}{rhs}{suffix}");
            let source = source.as_str();
            let e = f + 3 + rhs.len();
            let (green, exit, remainder) =
                run_statement_normalized(source, 0, LineEntry::InLine, None);
            assert_eq!(green.to_string(), source);
            assert_eq!(remainder, "");
            let NormalizedExit::Complete(Err(Either::Right(mut end)), LineEntry::InLine) = exit
            else {
                panic!("{source:?}: expected EOF InLine");
            };
            assert!(end.item.payload_view().is_eof());
            assert_eq!(emit_pending_leading_text(&mut end.item), "");
            let root = SyntaxNode::new_root(green);
            assert_eq!(root.kind(), Root);
            assert_eq!(root.parent(), None);
            assert_eq!(
                root.text_range(),
                rowan::TextRange::new(0.into(), (source.len() as u32).into())
            );
            children(&root, &[(Statement, true, 0..source.len(), source)]);
            let statement = root.first_child().unwrap();
            children(
                &statement,
                &[(declaration_kind, true, 0..source.len(), source)],
            );
            let declaration = statement.first_child().unwrap();
            let mut shell = vec![
                (keyword, false, 0..keyword_end, &source[..keyword_end]),
                (Whitespace, false, keyword_end..keyword_end + 1, " "),
                (
                    Identifier,
                    false,
                    keyword_end + 1..keyword_end + 2,
                    &source[keyword_end + 1..keyword_end + 2],
                ),
                (Whitespace, false, keyword_end + 2..keyword_end + 3, " "),
                (LBrace, false, keyword_end + 3..keyword_end + 4, "{"),
            ];
            if declaration_kind == StructDeclaration {
                shell.push((StructField, true, f..e, &source[f..e]));
            } else {
                shell.push((
                    EnumVariant,
                    true,
                    keyword_end + 4..e + 1,
                    &source[keyword_end + 4..e + 1],
                ));
                shell.push((Whitespace, false, e + 1..e + 2, " "));
            }
            shell.push((RBrace, false, source.len() - 1..source.len(), "}"));
            children(&declaration, &shell);
            let owner = declaration.first_child().unwrap();
            let field = if owner.kind() == EnumVariant {
                children(
                    &owner,
                    &[
                        (Whitespace, false, keyword_end + 4..keyword_end + 5, " "),
                        (Identifier, false, keyword_end + 5..keyword_end + 6, "A"),
                        (Whitespace, false, keyword_end + 6..keyword_end + 7, " "),
                        (LBrace, false, keyword_end + 7..f, "{"),
                        (StructField, true, f..e, &source[f..e]),
                        (RBrace, false, e..e + 1, "}"),
                    ],
                );
                owner.first_child().unwrap()
            } else {
                owner
            };
            let mut slots = vec![
                (Identifier, false, f..f + 1, "a"),
                (Colon, false, f + 1..f + 2, ":"),
                (Whitespace, false, f + 2..f + 3, " "),
                (Error, false, f + 3..f + 4, "@"),
            ];
            let error_end = if multileaf { f + 7 } else { f + 4 };
            if multileaf {
                slots.extend([
                    (Error, false, f + 4..f + 6, "  "),
                    (Error, false, f + 6..f + 7, "~"),
                ]);
            }
            if retry {
                slots.push((TypeExpression, true, error_end..e, &source[error_end..e]));
            }
            children(&field, &slots);
            if retry {
                children(
                    &field.first_child().unwrap(),
                    &[
                        (
                            Whitespace,
                            false,
                            error_end..e - 1,
                            &source[error_end..e - 1],
                        ),
                        (Identifier, false, e - 1..e, "T"),
                    ],
                );
            }

            // Identify the mandatory Type slot from complete ancestry and actual punctuation.
            let ancestry = field
                .ancestors()
                .map(|node| node.kind())
                .collect::<Vec<_>>();
            assert!(matches!(
                ancestry.as_slice(),
                [StructField, StructDeclaration, Statement, Root]
                    | [StructField, EnumVariant, EnumDeclaration, Statement, Root]
                    | [StructField, EnumVariant, ErrorDeclaration, Statement, Root]
            ));
            let owner = field.parent().unwrap();
            let native = owner.children_with_tokens().collect::<Vec<_>>();
            let index = native
                .iter()
                .position(|child| child.as_node() == Some(&field))
                .unwrap();
            assert_eq!(native[index - 1].kind(), LBrace);
            assert!(native[index - 1].as_token().is_some());
            assert_eq!(native[index + 1].kind(), RBrace);
            assert!(native[index + 1].as_token().is_some());
            let direct = field.children_with_tokens().collect::<Vec<_>>();
            assert_eq!(direct[0].kind(), Identifier);
            assert!(direct[0].as_token().is_some());
            assert_eq!(direct[1].kind(), Colon);
            assert!(direct[1].as_token().is_some());
            assert_eq!(direct[2].kind(), Whitespace);
            assert!(direct[2].as_token().is_some());
            let group = direct
                .iter()
                .skip(3)
                .take_while(|child| child.kind() == Error)
                .collect::<Vec<_>>();
            assert!(!group.is_empty());
            for fragment in &group {
                assert!(fragment.as_token().is_some());
                assert_eq!(fragment.parent().as_ref(), Some(&field));
            }
            for pair in group.windows(2) {
                assert_eq!(pair[0].text_range().end(), pair[1].text_range().start());
            }
            let range = usize::from(group[0].text_range().start())
                ..usize::from(group.last().unwrap().text_range().end());
            assert_eq!(range, f + 3..error_end);
            assert_eq!(direct.len(), 3 + group.len() + usize::from(retry));
            if retry {
                assert_eq!(direct[3 + group.len()].kind(), TypeExpression);
                assert!(direct[3 + group.len()].as_node().is_some());
            }
            assert!(
                !root
                    .descendants_with_tokens()
                    .any(|child| matches!(child.kind(), SyntaxKind::Missing | SyntaxKind::Invalid))
            );
            assert_eq!(
                root.descendants_with_tokens()
                    .filter(|child| child.kind() == Error)
                    .count(),
                group.len()
            );

            let expected = [(
                StructuralKind::ErrorGroup,
                "sentinel".len() + range.start.."sentinel".len() + range.end,
            )];
            let mut fresh = run_statement_structural_facts(source, 0);
            let NormalizedExit::Complete(Err(Either::Right(end)), LineEntry::InLine) =
                &mut fresh.exit
            else {
                panic!("{source:?}: seeded harness must also return EOF InLine");
            };
            assert!(end.item.payload_view().is_eof());
            assert_eq!(emit_pending_leading_text(&mut end.item), "");
            assert_eq!(fresh.green.to_string(), format!("sentinel{source}"));
            let seeded_root = SyntaxNode::new_root(fresh.green.clone());
            assert_eq!(
                seeded_root
                    .children()
                    .find(|node| node.kind() == Statement)
                    .unwrap()
                    .green(),
                statement.green()
            );
            assert_eq!(fresh.facts, expected);
            assert_eq!(fresh.mark, ());
            assert!(fresh.same_operators);
            assert_eq!(fresh.successor_origin, source.len());
            assert_eq!(fresh.remainder, "");
            let replay = run_statement_structural_facts(source, 0);
            assert_eq!(replay.green, fresh.green);
            assert_eq!(replay.facts, fresh.facts);
            assert_eq!(replay.mark, ());
            assert!(replay.same_operators);
            assert_same_exit(&fresh.exit, &replay.exit);
            assert_eq!(replay.successor_origin, fresh.successor_origin);
            assert_eq!(replay.remainder, fresh.remainder);
        }
    }
}

#[test]
fn tuple_and_positional_required_type_initial_error_have_direct_five_owner_slots() {
    use SyntaxKind::{
        EnumDeclaration, EnumKw, EnumVariant, Error, ErrorDeclaration, ErrorKw, Identifier, LBrace,
        LParen, RBrace, RParen, Root, Statement, StructDeclaration, StructField, StructKw,
        TypeExpression, Whitespace,
    };

    fn children(parent: &SyntaxNode, expected: &[(SyntaxKind, bool, Range<usize>, &str)]) {
        let actual = parent.children_with_tokens().collect::<Vec<_>>();
        assert_eq!(actual.len(), expected.len(), "{parent:#?}");
        for (child, (kind, node, range, text)) in actual.iter().zip(expected) {
            assert_eq!(child.parent().as_ref(), Some(parent));
            assert_eq!(child.kind(), *kind);
            assert_eq!(child.as_node().is_some(), *node);
            assert_eq!(child.as_token().is_some(), !node);
            assert_eq!(
                usize::from(child.text_range().start())..usize::from(child.text_range().end()),
                *range
            );
            assert_eq!(child.to_string(), *text);
        }
    }

    for (prefix, suffix, declaration_kind, keyword, k, tuple) in [
        ("struct S(", ")", StructDeclaration, StructKw, 6, true),
        ("enum E{A(", ")}", EnumDeclaration, EnumKw, 4, true),
        ("error E{A(", ")}", ErrorDeclaration, ErrorKw, 5, true),
        ("enum E{A ", "}", EnumDeclaration, EnumKw, 4, false),
        ("error E{A ", "}", ErrorDeclaration, ErrorKw, 5, false),
    ] {
        for (payload, retry, multileaf) in [
            ("@", false, false),
            ("@ T", true, false),
            ("@  ~   T", true, true),
        ] {
            let source = format!("{prefix}{payload}{suffix}");
            let source = source.as_str();
            let s = prefix.len();
            let e = s + payload.len();
            let (green, exit, remainder) =
                run_statement_normalized(source, 0, LineEntry::InLine, None);
            assert_eq!(green.to_string(), source);
            assert_eq!(remainder, "");
            let NormalizedExit::Complete(Err(Either::Right(mut end)), LineEntry::InLine) = exit
            else {
                panic!("{source:?}: expected EOF InLine");
            };
            assert!(end.item.payload_view().is_eof());
            assert_eq!(emit_pending_leading_text(&mut end.item), "");
            let root = SyntaxNode::new_root(green);
            assert_eq!(root.kind(), Root);
            assert_eq!(root.parent(), None);
            assert_eq!(
                root.text_range(),
                rowan::TextRange::new(0.into(), (source.len() as u32).into())
            );
            children(&root, &[(Statement, true, 0..source.len(), source)]);
            let statement = root.children().next().unwrap();
            children(
                &statement,
                &[(declaration_kind, true, 0..source.len(), source)],
            );
            let declaration = statement.children().next().unwrap();
            let is_struct = declaration_kind == StructDeclaration;
            let mut shell = vec![
                (keyword, false, 0..k, &source[..k]),
                (Whitespace, false, k..k + 1, " "),
                (Identifier, false, k + 1..k + 2, &source[k + 1..k + 2]),
            ];
            if is_struct {
                shell.extend([
                    (LParen, false, k + 2..s, "("),
                    (StructField, true, s..e, &source[s..e]),
                    (RParen, false, e..e + 1, ")"),
                ]);
            } else {
                let variant_end = e + usize::from(tuple);
                shell.extend([
                    (LBrace, false, k + 2..k + 3, "{"),
                    (
                        EnumVariant,
                        true,
                        k + 3..variant_end,
                        &source[k + 3..variant_end],
                    ),
                    (RBrace, false, variant_end..variant_end + 1, "}"),
                ]);
            }
            children(&declaration, &shell);
            let owner = if is_struct {
                declaration
                    .children()
                    .find(|node| node.kind() == StructField)
                    .unwrap()
            } else {
                let variant = declaration
                    .children()
                    .find(|node| node.kind() == EnumVariant)
                    .unwrap();
                if tuple {
                    children(
                        &variant,
                        &[
                            (Identifier, false, k + 3..k + 4, "A"),
                            (LParen, false, k + 4..s, "("),
                            (StructField, true, s..e, &source[s..e]),
                            (RParen, false, e..e + 1, ")"),
                        ],
                    );
                    variant
                        .children()
                        .find(|node| node.kind() == StructField)
                        .unwrap()
                } else {
                    variant
                }
            };
            let mut slots = Vec::new();
            if !tuple {
                slots.extend([
                    (Identifier, false, s - 2..s - 1, "A"),
                    (Whitespace, false, s - 1..s, " "),
                ]);
            }
            slots.push((Error, false, s..s + 1, "@"));
            let error_end = s + if multileaf { 4 } else { 1 };
            if multileaf {
                slots.extend([
                    (Error, false, s + 1..s + 3, "  "),
                    (Error, false, s + 3..s + 4, "~"),
                ]);
            }
            if retry {
                slots.push((TypeExpression, true, error_end..e, &source[error_end..e]));
            }
            children(&owner, &slots);
            if retry {
                let ty = owner
                    .children()
                    .find(|node| node.kind() == TypeExpression)
                    .unwrap();
                children(
                    &ty,
                    &[
                        (
                            Whitespace,
                            false,
                            error_end..e - 1,
                            &source[error_end..e - 1],
                        ),
                        (Identifier, false, e - 1..e, "T"),
                    ],
                );
            }

            // Select the slot from ancestry and ordered native children, before records.
            let ancestry = owner
                .ancestors()
                .map(|node| node.kind())
                .collect::<Vec<_>>();
            let direct = owner.children_with_tokens().collect::<Vec<_>>();
            let start = match ancestry.as_slice() {
                [StructField, StructDeclaration, Statement, Root]
                | [StructField, EnumVariant, EnumDeclaration, Statement, Root]
                | [StructField, EnumVariant, ErrorDeclaration, Statement, Root] => {
                    let parent = owner.parent().unwrap();
                    let native = parent.children_with_tokens().collect::<Vec<_>>();
                    let index = native
                        .iter()
                        .position(|child| child.as_node() == Some(&owner))
                        .unwrap();
                    assert_eq!(native[index - 1].kind(), LParen);
                    assert!(native[index - 1].as_token().is_some());
                    assert_eq!(native[index + 1].kind(), RParen);
                    assert!(native[index + 1].as_token().is_some());
                    0
                }
                [EnumVariant, EnumDeclaration, Statement, Root]
                | [EnumVariant, ErrorDeclaration, Statement, Root] => {
                    assert_eq!(direct[0].kind(), Identifier);
                    assert!(direct[0].as_token().is_some());
                    assert_eq!(direct[1].kind(), Whitespace);
                    assert!(direct[1].as_token().is_some());
                    2
                }
                _ => panic!("unexpected tuple/positional ancestry: {ancestry:?}"),
            };
            let group = direct
                .iter()
                .skip(start)
                .take_while(|child| child.kind() == Error)
                .collect::<Vec<_>>();
            assert!(!group.is_empty());
            for fragment in &group {
                assert!(fragment.as_token().is_some());
                assert_eq!(fragment.parent().as_ref(), Some(&owner));
            }
            for pair in group.windows(2) {
                assert_eq!(pair[0].text_range().end(), pair[1].text_range().start());
            }
            let range = usize::from(group[0].text_range().start())
                ..usize::from(group.last().unwrap().text_range().end());
            assert_eq!(range, s..error_end);
            assert_eq!(direct.len(), start + group.len() + usize::from(retry));
            if retry {
                let next = &direct[start + group.len()];
                assert_eq!(next.kind(), TypeExpression);
                assert!(next.as_node().is_some());
                assert_eq!(
                    group.last().unwrap().text_range().end(),
                    next.text_range().start()
                );
            }
            assert!(
                !root
                    .descendants_with_tokens()
                    .any(|child| matches!(child.kind(), SyntaxKind::Missing | SyntaxKind::Invalid))
            );
            assert_eq!(
                root.descendants_with_tokens()
                    .filter(|child| child.kind() == Error)
                    .count(),
                group.len()
            );

            let expected = [(
                StructuralKind::ErrorGroup,
                "sentinel".len() + range.start.."sentinel".len() + range.end,
            )];
            let mut fresh = run_statement_structural_facts(source, 0);
            let NormalizedExit::Complete(Err(Either::Right(end)), LineEntry::InLine) =
                &mut fresh.exit
            else {
                panic!("{source:?}: seeded harness must return EOF InLine");
            };
            assert!(end.item.payload_view().is_eof());
            assert_eq!(emit_pending_leading_text(&mut end.item), "");
            assert_eq!(fresh.green.to_string(), format!("sentinel{source}"));
            let seeded_root = SyntaxNode::new_root(fresh.green.clone());
            assert_eq!(
                seeded_root
                    .children()
                    .find(|node| node.kind() == Statement)
                    .unwrap()
                    .green(),
                statement.green()
            );
            assert_eq!(fresh.facts, expected);
            assert_eq!(fresh.mark, ());
            assert!(fresh.same_operators);
            assert_eq!(fresh.successor_origin, source.len());
            assert_eq!(fresh.remainder, "");
            let replay = run_statement_structural_facts(source, 0);
            assert_eq!(replay.green, fresh.green);
            assert_eq!(replay.facts, fresh.facts);
            assert_eq!(replay.mark, ());
            assert!(replay.same_operators);
            assert_same_exit(&fresh.exit, &replay.exit);
            assert_eq!(replay.successor_origin, fresh.successor_origin);
            assert_eq!(replay.remainder, fresh.remainder);
        }
    }
}

#[test]
fn required_caller_role_never_remaps_malformed_or_nested_type_recovery() {
    for (source, expected) in [
        ("type T = @", (StructuralKind::ErrorGroup, 17..18)),
        ("type T = A->", (StructuralKind::Missing, (20)..(20))),
        ("type T = {a:}", field_missing(20)),
    ] {
        let fresh = run_statement_structural_facts(source, 0);
        assert_eq!(fresh.green.to_string(), format!("sentinel{source}"));
        assert_eq!(fresh.facts, [expected.clone()], "{source:?}");
        let replay = run_statement_structural_facts(source, 0);
        assert_eq!(replay.green, fresh.green);
        assert_eq!(replay.facts, fresh.facts);
    }
    let expected = [missing(0, 2)];
    let (green, _, facts) = run_pattern_with_structural_diagnostics("x:");
    assert_eq!(facts, expected);
    assert_eq!(green.to_string(), "x:");
}

#[test]
fn required_derives_role_preserves_the_nominal_declaration_terminator() {
    let source = "type T derives via key;";
    for origin in [0, 41] {
        let expected = [missing(0, "sentinel".len() + 14)];
        let fresh = run_statement_structural_facts(source, origin);
        assert_eq!(fresh.green.to_string(), "sentineltype T derives via key");
        assert_eq!(fresh.facts, expected);
        let NormalizedExit::Complete(Err(Either::Left(item)), line) = &fresh.exit else {
            panic!("nominal TypeDeclaration returns its terminator")
        };
        let (control, next, control_line, remainder, _, _) =
            scan_type_item_control(";", origin + 22, &OperatorTable::empty());
        assert_eq!(item, &control);
        assert_eq!(*line, control_line);
        assert_eq!(fresh.successor_origin, next);
        assert_eq!(fresh.remainder, remainder);
        let replay = run_statement_structural_facts(source, origin);
        assert_eq!(replay.green, fresh.green);
        assert_eq!(replay.facts, fresh.facts);
        assert_same_exit(&fresh.exit, &replay.exit);
    }
}

fn field_missing(at: usize) -> ExpectedStructural {
    crate::tests::type_expr::record_field_recovery::field_record(0, at..at, false)
}
