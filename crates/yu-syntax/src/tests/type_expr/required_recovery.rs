use crate::recovery_record::{
    ActDeclarationRole, CastRole, DeclarationRole, DerivesRole, EnumDeclarationRole,
    ErrorDeclarationRole, ImplRole, PatternRole, RoleDeclarationRole, StructRole,
    TypeDeclarationRole, VariantDeclarationRole,
};
use crate::tests::type_expr::*;

pub(super) fn missing(id: u32, role: GrammarRole, at: usize) -> CommittedRecoveryRecord {
    CommittedRecoveryRecord {
        id: DiagnosticId(id),
        site: RecoverySiteKey {
            role,
            range: at..at,
        },
        kind: RecoveryKind::Missing,
        unexpected: Arc::from([]),
        expectations: Arc::from([SyntaxExpectation {
            role,
            expected: ExpectedSyntax::TypeExpression,
            range: at..at,
            sources: ExpectationSources::COMMITTED_RECOVERY_RULE,
        }]),
        primary_expectation: 0,
    }
}

#[allow(clippy::too_many_arguments)]
fn run_required<'source>(
    source: &'source str,
    role: GrammarRole,
    origin: usize,
    line: LineEntry,
    fence: Option<&FenceBoundary>,
    emit_leading: bool,
    frozen: Option<&[CommittedRecoveryRecord]>,
) -> (ContextualTypeRun<'source>, bool) {
    let operators = OperatorTable::empty();
    let mut input = source;
    let mut recover = Recover::new_for_test(&operators);
    let mark = crate::cursor::LexRecover::new_for_test(recover.operators()).mark();
    let mut output = frozen.map_or_else(GreenNodeBuilder::new, |records| {
        recover = Recover::reconcile_for_test(recover.operators(), records);
        GreenNodeBuilder::new()
    });
    output.start_node(SyntaxKind::Root.into());
    seed_identifier(&mut output);
    // A prior committed slot and CST sibling must survive this total attempt.
    output.start_node(SyntaxKind::Missing.into());
    output.finish_node();
    commit_record_draft(
        &mut recover,
        &missing(0, GrammarRole::Type(TypeRole::ArrowRhs), origin),
    );
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
        crate::cursor::SyntaxIn::new(&mut input, &mut recover, &mut output), primary, role, 0,
        crate::lexical::stops::STOP_WITH, crate::type_expr::TypeOuterBoundary::WITH,
        next_origin, next_line, fence,
        Some(crate::ambient_claim::AmbientClaimView::root_statement(0)).into());
    let slots = recover.recovery_slot_count();
    let diagnostics = recover.diagnostic_position();
    output.finish_node();
    let same_operators = std::ptr::eq(recover.operators(), &operators);
    let (green, records) = (output.finish(), recover.finish_recoveries_for_test());
    (
        ContextualTypeRun {
            green,
            exit,
            successor_origin: origin + source.len() - input.len(),
            remainder: input,
            records,
            slots,
            diagnostics,
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
fn required_missing_uses_the_explicit_role_and_remaining_extent_with_seeded_frozen_output() {
    for role in [
        GrammarRole::Type(TypeRole::Primary),
        GrammarRole::Pattern(PatternRole::TypeAnnotation),
        GrammarRole::Declaration(DeclarationRole::Type(TypeDeclarationRole::Rhs)),
    ] {
        for origin in [0, 41] {
            for (source, emit_leading, at, emitted) in [
                ("", false, 0, ""),
                (" ", false, 0, ""),
                (" ", true, 1, " "),
                (" /*é*/ )tail", false, 0, ""),
                (" /*é*/ )tail", true, 8, " /*é*/ "),
                ("\n)tail", false, 0, ""),
                (" with tail", false, 0, ""),
            ] {
                let expected = [
                    missing(0, GrammarRole::Type(TypeRole::ArrowRhs), origin),
                    missing(1, role, origin + at),
                ];
                let (fresh, found) = run_required(
                    source,
                    role,
                    origin,
                    LineEntry::InLine,
                    None,
                    emit_leading,
                    None,
                );
                assert!(!found);
                assert_eq!(fresh.green.to_string(), format!("sentinel{emitted}"));
                assert_eq!(fresh.records, expected, "{source:?}");
                assert_eq!(fresh.slots, 2);
                assert_eq!(fresh.diagnostics, (Some(2), 0));
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
                let frozen = frozen_recovery_ids(&expected);
                let (replay, found) = run_required(
                    source,
                    role,
                    origin,
                    LineEntry::InLine,
                    None,
                    emit_leading,
                    Some(&frozen),
                );
                assert!(!found);
                assert_eq!(replay.green, fresh.green);
                assert_eq!(replay.records, frozen);
                assert_eq!(replay.slots, 2);
                assert_eq!(replay.diagnostics, (Some(9), 2));
                assert_eq!(replay.mark, ());
                assert!(replay.same_operators);
                assert_same_exit(&fresh.exit, &replay.exit);
                assert_eq!(replay.successor_origin, fresh.successor_origin);
                assert_eq!(replay.remainder, fresh.remainder);
            }
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
    let role = GrammarRole::Pattern(PatternRole::TypeAnnotation);
    let source = "> > \r\n> > ```\nouter";
    for origin in [0, 41] {
        let expected = [
            missing(0, GrammarRole::Type(TypeRole::ArrowRhs), origin),
            missing(1, role, origin + 6),
        ];
        let (fresh, found) = run_required(
            source,
            role,
            origin,
            LineEntry::PhysicalStart,
            Some(&fence),
            false,
            None,
        );
        assert!(!found);
        assert_eq!(fresh.green.to_string(), "sentinel");
        assert_eq!(fresh.records, expected);
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
        let frozen = frozen_recovery_ids(&expected);
        let (replay, found) = run_required(
            source,
            role,
            origin,
            LineEntry::PhysicalStart,
            Some(&fence),
            false,
            Some(&frozen),
        );
        assert!(!found);
        assert_eq!(replay.green, fresh.green);
        assert_eq!(replay.records, frozen);
        assert_eq!(replay.slots, 2);
        assert_eq!(replay.diagnostics, (Some(9), 2));
        assert_same_exit(&fresh.exit, &replay.exit);
        assert_eq!(replay.successor_origin, fresh.successor_origin);
        assert_eq!(replay.remainder, fresh.remainder);
    }
}

pub(super) fn run_statement_records<'source>(
    source: &'source str,
    origin: usize,
    frozen: Option<&[CommittedRecoveryRecord]>,
) -> ContextualTypeRun<'source> {
    let operators = OperatorTable::empty();
    let mut input = source;
    let mut recover = Recover::new_for_test(&operators);
    let mark = crate::cursor::LexRecover::new_for_test(recover.operators()).mark();
    let mut output = frozen.map_or_else(GreenNodeBuilder::new, |records| {
        recover = Recover::reconcile_for_test(recover.operators(), records);
        GreenNodeBuilder::new()
    });
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
    let slots = recover.recovery_slot_count();
    let diagnostics = recover.diagnostic_position();
    output.finish_node();
    let same_operators = std::ptr::eq(recover.operators(), &operators);
    let (green, records) = (output.finish(), recover.finish_recoveries_for_test());
    ContextualTypeRun {
        green,
        exit,
        records,
        successor_origin: origin + source.len() - input.len(),
        remainder: input,
        slots,
        diagnostics,
        mark,
        same_operators,
    }
}

#[test]
fn required_type_real_declaration_callers_publish_their_own_missing_roles() {
    use DeclarationRole as D;
    for origin in [0, 41] {
        for (source, role, at) in [
            ("type T =", D::Type(TypeDeclarationRole::Rhs), 8),
            ("type T = ", D::Type(TypeDeclarationRole::Rhs), 9),
            ("struct S {a:}", D::Struct(StructRole::FieldType), 12),
            ("struct S:\n  a:", D::Struct(StructRole::FieldType), 14),
            (
                "enum E { A from }",
                D::Enum(EnumDeclarationRole::Variant(
                    VariantDeclarationRole::FromType,
                )),
                16,
            ),
            (
                "error E { A from }",
                D::Error(ErrorDeclarationRole::Variant(
                    VariantDeclarationRole::FromType,
                )),
                17,
            ),
            (
                "enum E { A {a:} }",
                D::Enum(EnumDeclarationRole::Variant(
                    VariantDeclarationRole::NamedFieldType,
                )),
                14,
            ),
            (
                "error E { A {a:} }",
                D::Error(ErrorDeclarationRole::Variant(
                    VariantDeclarationRole::NamedFieldType,
                )),
                15,
            ),
            ("role ;", D::Role(RoleDeclarationRole::Head), 5),
            ("impl ;", D::Impl(ImplRole::Head), 5),
            ("impl T: ;", D::Impl(ImplRole::Description), 8),
            ("act;", D::Act(ActDeclarationRole::Head), 3),
            ("act A = ;", D::Act(ActDeclarationRole::Source), 7),
            ("cast(x): ;", D::Cast(CastRole::TargetType), 9),
        ] {
            let expected = [missing(0, GrammarRole::Declaration(role), origin + at)];
            let fresh = run_statement_records(source, origin, None);
            assert_eq!(
                fresh.green.to_string(),
                format!("sentinel{source}"),
                "{source:?}"
            );
            assert_eq!(fresh.remainder, "", "{source:?}");
            assert_eq!(fresh.records, expected, "{source:?}");
            assert_eq!(fresh.slots, 1);
            assert_eq!(fresh.diagnostics, (Some(1), 0));
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
            let frozen = frozen_recovery_ids(&expected);
            let replay = run_statement_records(source, origin, Some(&frozen));
            assert_eq!(replay.green, fresh.green);
            assert_eq!(replay.records, frozen);
            assert_eq!(replay.slots, 1);
            assert_eq!(replay.diagnostics, (Some(8), 1));
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
        let role = GrammarRole::Declaration(match ancestry.as_slice() {
            [
                Missing,
                TypeExpression,
                StructField,
                StructDeclaration,
                Statement,
                Root,
            ] => DeclarationRole::Struct(StructRole::FieldType),
            [
                Missing,
                TypeExpression,
                StructField,
                EnumVariant,
                EnumDeclaration,
                Statement,
                Root,
            ] => DeclarationRole::Enum(EnumDeclarationRole::Variant(
                VariantDeclarationRole::NamedFieldType,
            )),
            [
                Missing,
                TypeExpression,
                StructField,
                EnumVariant,
                ErrorDeclaration,
                Statement,
                Root,
            ] => DeclarationRole::Error(ErrorDeclarationRole::Variant(
                VariantDeclarationRole::NamedFieldType,
            )),
            _ => panic!("unexpected named-field ancestry: {ancestry:?}"),
        });
        let range = missing_node.text_range();
        assert!(range.is_empty());
        assert_eq!(usize::from(range.start())..usize::from(range.end()), at..at);
        let structural_projection = type_expr
            .children()
            .map(|child| {
                assert_eq!(child, missing_node);
                assert_eq!(child.kind(), Missing);
                assert!(child.children_with_tokens().next().is_none());
                (
                    role,
                    [ExpectedSyntax::TypeExpression],
                    0,
                    child.text_range(),
                )
            })
            .collect::<Vec<_>>();
        assert_eq!(
            structural_projection,
            [(role, [ExpectedSyntax::TypeExpression], 0, range)]
        );
        let expected = [missing(0, role, usize::from(range.start()))];
        let mut fresh = run_statement_records(source, 0, None);
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
        assert_eq!(fresh.records, expected);
        assert_eq!(fresh.slots, 1);
        assert_eq!(fresh.diagnostics, (Some(1), 0));
        assert_eq!(fresh.mark, ());
        assert!(fresh.same_operators);
        assert_eq!(fresh.successor_origin, source.len());
        assert_eq!(fresh.remainder, "");
        let frozen = frozen_recovery_ids(&expected);
        let replay = run_statement_records(source, 0, Some(&frozen));
        assert_eq!(replay.green, fresh.green);
        assert_eq!(replay.records, frozen);
        assert_eq!(replay.slots, 1);
        assert_eq!(replay.diagnostics, (Some(8), 1));
        assert_eq!(replay.mark, ());
        assert!(replay.same_operators);
        assert_same_exit(&fresh.exit, &replay.exit);
        assert_eq!(replay.successor_origin, fresh.successor_origin);
        assert_eq!(replay.remainder, fresh.remainder);
    }
}

#[test]
fn required_caller_role_never_remaps_malformed_or_nested_type_recovery() {
    for (source, expected) in [
        (
            "type T = @",
            expected_required_type_primary_error(
                0,
                9..10,
                Arc::from([UnexpectedSyntax::Token {
                    range: 9..10,
                    category: UnexpectedCategory::OtherCharacter,
                }]),
            ),
        ),
        (
            "type T = A->",
            expected_type_expression_missing(0, TypeRole::ArrowRhs, 12),
        ),
        ("type T = {a:}", field_missing(12)),
    ] {
        let fresh = run_statement_records(source, 0, None);
        assert_eq!(fresh.green.to_string(), format!("sentinel{source}"));
        assert_eq!(fresh.records, [expected.clone()], "{source:?}");
        let frozen = frozen_recovery_ids(&[expected]);
        let replay = run_statement_records(source, 0, Some(&frozen));
        assert_eq!(replay.green, fresh.green);
        assert_eq!(replay.records, frozen);
    }
    let expected = [missing(
        0,
        GrammarRole::Pattern(PatternRole::TypeAnnotation),
        2,
    )];
    let (green, _, records) = run_pattern_with_recoveries("x:", None);
    assert_eq!(records, expected);
    let frozen = frozen_recovery_ids(&expected);
    let (replayed, _, records) = run_pattern_with_recoveries("x:", Some(&frozen));
    assert_eq!(replayed, green);
    assert_eq!(records, frozen);
}

#[test]
fn required_derives_role_preserves_the_nominal_declaration_terminator() {
    let source = "type T derives via key;";
    for origin in [0, 41] {
        let role = GrammarRole::Declaration(DeclarationRole::Derives(DerivesRole::RoleReference));
        let expected = [missing(0, role, origin + 14)];
        let fresh = run_statement_records(source, origin, None);
        assert_eq!(fresh.green.to_string(), "sentineltype T derives via key");
        assert_eq!(fresh.records, expected);
        let NormalizedExit::Complete(Err(Either::Left(item)), line) = &fresh.exit else {
            panic!("nominal TypeDeclaration returns its terminator")
        };
        let (control, next, control_line, remainder, _, _) =
            scan_type_item_control(";", origin + 22, &OperatorTable::empty());
        assert_eq!(item, &control);
        assert_eq!(*line, control_line);
        assert_eq!(fresh.successor_origin, next);
        assert_eq!(fresh.remainder, remainder);
        let frozen = frozen_recovery_ids(&expected);
        let replay = run_statement_records(source, origin, Some(&frozen));
        assert_eq!(replay.green, fresh.green);
        assert_eq!(replay.records, frozen);
        assert_same_exit(&fresh.exit, &replay.exit);
        assert_eq!(replay.slots, 1);
        assert_eq!(replay.diagnostics, (Some(8), 1));
    }
}

fn field_missing(at: usize) -> CommittedRecoveryRecord {
    crate::tests::type_expr::record_field_recovery::field_record(
        0,
        TypeRole::RecordFieldType,
        at..at,
        false,
    )
}
