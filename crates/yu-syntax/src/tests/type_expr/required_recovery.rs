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
    let mut recover = Recover::new(&operators);
    let mark = recover.mark();
    let mut output = frozen.map_or_else(GreenNodeBuilder::new, GreenNodeBuilder::reconcile);
    output.start_node(SyntaxKind::Root.into());
    seed_identifier(&mut output);
    // A prior committed slot and CST sibling must survive this total attempt.
    output.start_node(SyntaxKind::Missing.into());
    output.finish_node();
    commit_record_draft(
        &mut output,
        &missing(0, GrammarRole::Type(TypeRole::ArrowRhs), origin),
    );
    let (mut primary, next_origin, next_line) = crate::type_expr::type_nud_item_normalized(
        In::new(&mut input, &mut recover, &mut output),
        origin,
        line,
        fence,
    );
    if emit_leading {
        primary.emit_all_remaining_leading(&mut output);
    }
    let (exit, found) = crate::type_expr::required_type_expr_with_caller_stops_and_outer_boundary_normalized_with_ambient(
        In::new(&mut input, &mut recover, &mut output), primary, role, 0,
        crate::lexical::stops::STOP_WITH, crate::type_expr::TypeOuterBoundary::WITH,
        next_origin, next_line, fence,
        Some(crate::ambient_claim::AmbientClaimView::root_statement(0)).into());
    let slots = output.recovery_slot_count();
    let diagnostics = output.diagnostic_position();
    output.finish_node();
    let (green, records) = output.finish_with_recoveries();
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
            same_operators: std::ptr::eq(recover.operators(), &operators),
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
                    assert_eq!(
                        leading_output.finish_with_recoveries().0.to_string(),
                        emitted
                    );
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
    let mut recover = Recover::new(&operators);
    let mark = recover.mark();
    let mut output = frozen.map_or_else(GreenNodeBuilder::new, GreenNodeBuilder::reconcile);
    output.start_node(SyntaxKind::Root.into());
    seed_identifier(&mut output);
    let mut exit = statement_normalized(
        In::new(&mut input, &mut recover, &mut output),
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
    let slots = output.recovery_slot_count();
    let diagnostics = output.diagnostic_position();
    output.finish_node();
    let (green, records) = output.finish_with_recoveries();
    ContextualTypeRun {
        green,
        exit,
        records,
        successor_origin: origin + source.len() - input.len(),
        remainder: input,
        slots,
        diagnostics,
        mark,
        same_operators: std::ptr::eq(recover.operators(), &operators),
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
