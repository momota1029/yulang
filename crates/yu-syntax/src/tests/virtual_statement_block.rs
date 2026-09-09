use crate::recovery_record::{
    DiagnosticId, ExpectationSources, ExpectedSyntax, GrammarRole, RecoveryKind, RecoverySiteKey,
    StatementRole, SyntaxExpectation, UnexpectedCategory, UnexpectedSyntax,
};
use crate::tests::support::*;
use std::{ops::Range, sync::Arc};

pub(super) fn virtual_record(
    id: u32,
    role: StatementRole,
    kind: RecoveryKind,
    range: Range<usize>,
) -> CommittedRecoveryRecord {
    let expected = match role {
        StatementRole::Starter => ExpectedSyntax::Statement,
        StatementRole::Separator => ExpectedSyntax::StatementSeparator,
        _ => unreachable!(),
    };
    let role = GrammarRole::Statement(role);
    CommittedRecoveryRecord {
        id: DiagnosticId(id),
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
                category: UnexpectedCategory::OtherCharacter,
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

#[test]
fn virtual_selected_slots_have_exact_fresh_shifted_and_frozen_records() {
    use RecoveryKind::{Error, Missing};
    use StatementRole::{Separator, Starter};
    for (source, slots) in [
        (
            ",;}",
            vec![(Starter, Missing, 0..0), (Starter, Missing, 1..1)],
        ),
        (
            "; ,}",
            vec![(Starter, Missing, 0..0), (Starter, Missing, 1..1)],
        ),
        ("a,}", vec![]),
        ("a;}", vec![]),
        ("role R; value}", vec![(Separator, Missing, 7..7)]),
        (" @ @ α}", vec![(Starter, Error, 0..4)]),
        (" @ 💥 α}", vec![(Starter, Error, 0..7)]),
        ("@ role R;}", vec![(Starter, Error, 0..1)]),
        ("@ \"α\"}", vec![(Starter, Error, 0..1)]),
        ("a @ value}", vec![(Starter, Error, 1..3)]),
        (
            " , @}",
            vec![(Starter, Missing, 0..0), (Starter, Error, 3..4)],
        ),
        (" \t}", vec![]),
    ] {
        for origin in [0, 8100] {
            let expected: Vec<_> = slots
                .iter()
                .enumerate()
                .map(|(id, (role, kind, range))| {
                    virtual_record(
                        id as u32,
                        *role,
                        *kind,
                        origin + range.start..origin + range.end,
                    )
                })
                .collect();
            let mut fresh = None;
            for frozen in [None, Some(expected.as_slice())] {
                let operators = OperatorTable::empty();
                let mut recover = Recover::new_for_test(&operators);
                let mut input = source;
                let mut output = frozen
                    .map(|records| {
                        recover = Recover::reconcile_for_test(recover.operators(), records);
                        GreenNodeBuilder::new()
                    })
                    .unwrap_or_else(GreenNodeBuilder::new);
                output.start_node(SyntaxKind::Root.into());
                let exit = virtual_statement_block_normalized(
                    crate::cursor::SyntaxIn::new(&mut input, &mut recover, &mut output),
                    origin,
                    LineEntry::InLine,
                    None,
                    None.into(),
                );
                output.finish_node();
                let (green, records) = (output.finish(), recover.finish_recoveries_for_test());
                assert_eq!(records, expected, "{source:?} at {origin}");
                let VirtualStatementBlockExit::Close(item, _) = exit else {
                    panic!("pending close for {source:?}")
                };
                assert_eq!(item.payload_view().token_kind(), Some(TokenKind::RBrace));
                assert_eq!(input, "");
                if let Some(fresh) = &fresh {
                    assert_eq!(&green, fresh);
                } else {
                    fresh = Some(green);
                }
            }
        }
    }
}

#[test]
fn virtual_error_keeps_terminal_leading_and_source_suffix() {
    for (source, leading, remainder, fence) in [
        (" @ \t}tail", " \t", "tail", None),
        (" @ \t", " \t", "", None),
        (" @\n", "\n", "", None),
        (" @\r\n", "\r\n", "", None),
        (
            " @\r\n> > ```\r\nouter",
            "\r\n",
            "> > ```\r\nouter",
            Some(active_fence()),
        ),
    ] {
        let operators = OperatorTable::empty();
        let mut recover = Recover::new_for_test(&operators);
        let mut input = source;
        let mut output = GreenNodeBuilder::new();
        output.start_node(SyntaxKind::Root.into());
        let exit = virtual_statement_block_normalized(
            crate::cursor::SyntaxIn::new(&mut input, &mut recover, &mut output),
            300,
            LineEntry::InLine,
            fence.as_ref(),
            None.into(),
        );
        output.finish_node();
        let (green, records) = (output.finish(), recover.finish_recoveries_for_test());
        assert_eq!(green.to_string(), " @");
        assert_eq!(
            records,
            [virtual_record(
                0,
                StatementRole::Starter,
                RecoveryKind::Error,
                300..302
            )]
        );
        let (VirtualStatementBlockExit::Close(mut item, _)
        | VirtualStatementBlockExit::Boundary(mut item, _)) = exit;
        let pending_leading = if item.payload_view().is_boundary() {
            let (leading, boundary) = emit_terminal_leading_text(item);
            assert_eq!(boundary.coordinate(), 304);
            leading
        } else {
            emit_pending_leading_text(&mut item)
        };
        assert_eq!(pending_leading, leading);
        assert_eq!(input, remainder);
    }
}

#[test]
fn virtual_slots_preserve_seeded_and_frozen_ids_then_allocate_above_them() {
    for (source, role, kind, range) in [
        (",}", StatementRole::Starter, RecoveryKind::Missing, 0..0),
        (
            "role R; value}",
            StatementRole::Separator,
            RecoveryKind::Missing,
            7..7,
        ),
        (" @}", StatementRole::Starter, RecoveryKind::Error, 0..2),
    ] {
        let seed = virtual_record(7, StatementRole::Starter, RecoveryKind::Missing, 0..0);
        let reused = virtual_record(19, role, kind, 100 + range.start..100 + range.end);
        let frozen = [seed.clone(), reused.clone()];
        let operators = OperatorTable::empty();
        let mut recover = Recover::new_for_test(&operators);
        let mut output = {
            recover = Recover::reconcile_for_test(recover.operators(), &frozen);
            GreenNodeBuilder::new()
        };
        output.start_node(SyntaxKind::Root.into());
        output.start_node(SyntaxKind::Missing.into());
        output.finish_node();
        recover.commit_recovery_for_test(crate::cursor::recovery::RecoveryDraft::new(
            seed.site.clone(),
            seed.kind,
            seed.unexpected.clone(),
            seed.expectations.clone(),
            0,
        ));
        for origin in [100, 200] {
            let mut input = source;
            let exit = virtual_statement_block_normalized(
                crate::cursor::SyntaxIn::new(&mut input, &mut recover, &mut output),
                origin,
                LineEntry::InLine,
                None,
                None.into(),
            );
            assert!(matches!(exit, VirtualStatementBlockExit::Close(_, _)));
        }
        output.finish_node();
        let (_, records) = (output.finish(), recover.finish_recoveries_for_test());
        assert_eq!(
            records,
            [
                seed,
                reused,
                virtual_record(20, role, kind, 200 + range.start..200 + range.end)
            ]
        );
    }
}

#[test]
fn virtual_error_extent_includes_owned_foreign_prefix() {
    let fence = active_fence();
    let expected = [virtual_record(
        0,
        StatementRole::Starter,
        RecoveryKind::Error,
        400..410,
    )];
    for frozen in [None, Some(expected.as_slice())] {
        let operators = OperatorTable::empty();
        let mut recover = Recover::new_for_test(&operators);
        let mut input = "> > @ 💥 α}";
        let mut output = frozen
            .map(|records| {
                recover = Recover::reconcile_for_test(recover.operators(), records);
                GreenNodeBuilder::new()
            })
            .unwrap_or_else(GreenNodeBuilder::new);
        output.start_node(SyntaxKind::Root.into());
        let exit = virtual_statement_block_normalized(
            crate::cursor::SyntaxIn::new(&mut input, &mut recover, &mut output),
            400,
            LineEntry::PhysicalStart,
            Some(&fence),
            None.into(),
        );
        output.finish_node();
        let (green, records) = (output.finish(), recover.finish_recoveries_for_test());
        assert_eq!(records, expected);
        assert_eq!(green.to_string(), "> > @ 💥 α");
        assert!(matches!(exit, VirtualStatementBlockExit::Close(_, _)));
        assert_eq!(input, "");
    }
}

use crate::{
    SourceText, SyntaxEnvironment,
    lexical::yumark::{FenceOpener, FencePrefixPolicy},
    literal::{
        StringLiteralExit, scan_string_opener_witness,
        string_literal_with_virtual_statements_witness,
    },
    parse_file, scan_header,
    virtual_statement_block::{VirtualStatementBlockExit, virtual_statement_block_normalized},
};

fn plain_fence() -> FenceBoundary {
    FenceBoundary {
        opener: FenceOpener {
            line: 0,
            marker: 0..3,
            marker_width: 3,
        },
        prefix_policy: FencePrefixPolicy::None,
        close_column: 0,
    }
}

fn active_fence() -> FenceBoundary {
    FenceBoundary {
        opener: FenceOpener {
            line: 0,
            marker: 0..3,
            marker_width: 3,
        },
        prefix_policy: FencePrefixPolicy::ActivePrefixQuote { depth: 2, base: 0 },
        close_column: 0,
    }
}

fn run_virtual_string<'source>(
    source: &'source str,
    origin: usize,
    fence: &FenceBoundary,
) -> (GreenNode, StringLiteralExit, &'source str) {
    let operators = OperatorTable::empty();
    let mut recover = Recover::new_for_test(&operators);
    let mut input = source;
    let (opener, mode) = scan_string_opener_witness(chasa_recover::In::new(
        &mut input,
        &mut crate::cursor::LexRecover::new_for_test(recover.operators()),
        (),
    ))
    .expect("string opener");
    let interior_origin = origin
        .checked_add(opener.payload_view().spelling().expect("opener text").len())
        .expect("literal origin");
    let mut builder = GreenNodeBuilder::new();
    builder.start_node(SyntaxKind::Root.into());
    let exit = string_literal_with_virtual_statements_witness(
        crate::cursor::SyntaxIn::new(&mut input, &mut recover, &mut builder),
        opener,
        mode,
        interior_origin,
        fence,
    );
    builder.finish_node();
    (
        (builder.finish(), recover.finish_recoveries_for_test()).0,
        exit,
        input,
    )
}

fn count(green: &GreenNode, kind: SyntaxKind) -> usize {
    if kind == SyntaxKind::Error {
        return crate::tests::recovery_output::recovery_groups(&SyntaxNode::new_root(
            green.clone(),
        ))
        .len();
    }
    SyntaxNode::new_root(green.clone())
        .descendants()
        .filter(|node| node.kind() == kind)
        .count()
}

fn token_count(green: &GreenNode, kind: SyntaxKind) -> usize {
    SyntaxNode::new_root(green.clone())
        .descendants_with_tokens()
        .filter_map(|element| element.into_token())
        .filter(|token| token.kind() == kind)
        .count()
}

#[test]
fn virtual_statement_block_accepts_empty_and_leaves_close_leading_to_the_interpolation() {
    let source = "\"%{ \t}後\"tail";
    let (green, exit, remainder) = run_virtual_string(source, 0, &plain_fence());
    assert_eq!(exit, StringLiteralExit::Complete);
    assert_eq!(green.to_string(), "\"%{ \t}後\"");
    assert_eq!(remainder, "tail");
    assert_eq!(count(&green, SyntaxKind::Statement), 0);
    assert_eq!(count(&green, SyntaxKind::BlockStatementSeparator), 0);
    assert_eq!(count(&green, SyntaxKind::BracedStatementBlockExpression), 0);
    assert_eq!(count(&green, SyntaxKind::Missing), 0);
    assert_eq!(
        token_count(&green, SyntaxKind::StringInterpolationCloseBrace),
        1
    );
    let root = SyntaxNode::new_root(green);
    let interpolation = root
        .descendants()
        .find(|node| node.kind() == SyntaxKind::StringInterpolation)
        .expect("interpolation");
    assert_eq!(
        interpolation
            .children_with_tokens()
            .map(|element| (element.kind(), element.to_string()))
            .collect::<Vec<_>>(),
        [
            (SyntaxKind::StringInterpolationPercent, "%".to_owned()),
            (SyntaxKind::StringInterpolationOpenBrace, "{".to_owned()),
            (SyntaxKind::StringInterpolationBody, "".to_owned()),
            (SyntaxKind::Whitespace, " \t".to_owned()),
            (SyntaxKind::StringInterpolationCloseBrace, "}".to_owned()),
        ]
    );
}

#[test]
fn virtual_statement_block_returns_the_exact_unmodified_close_item() {
    let operators = OperatorTable::empty();
    let mut recover = Recover::new_for_test(&operators);
    let mut input = " \t}tail";
    let mut builder = GreenNodeBuilder::new();
    builder.start_node(SyntaxKind::Root.into());
    let exit = virtual_statement_block_normalized(
        crate::cursor::SyntaxIn::new(&mut input, &mut recover, &mut builder),
        400,
        LineEntry::InLine,
        Some(&plain_fence()),
        None.into(),
    );
    builder.finish_node();
    let green = finish_without_recoveries(builder, recover);
    let VirtualStatementBlockExit::Close(mut item, LineEntry::InLine) = exit else {
        panic!("empty virtual block must borrow its close")
    };
    assert_eq!(item.payload_view().token_kind(), Some(TokenKind::RBrace));
    assert_eq!(emit_pending_leading_text(&mut item), " \t");
    assert_eq!(green.to_string(), "");
    assert_eq!(input, "tail");
}

#[test]
fn virtual_statement_block_owns_comma_semicolon_lf_and_crlf_sequences() {
    let source = "\"%{a,b;c\nd\r\ne\n}後\"tail";
    let (green, exit, remainder) = run_virtual_string(source, 300, &plain_fence());
    assert_eq!(exit, StringLiteralExit::Complete);
    assert_eq!(green.to_string(), "\"%{a,b;c\nd\r\ne\n}後\"");
    assert_eq!(remainder, "tail");
    assert_eq!(count(&green, SyntaxKind::Statement), 5);
    assert_eq!(count(&green, SyntaxKind::BlockStatementSeparator), 4);
    assert_eq!(count(&green, SyntaxKind::Error), 0);
    assert_eq!(count(&green, SyntaxKind::Missing), 0);
    assert_eq!(
        token_count(&green, SyntaxKind::StringInterpolationCloseBrace),
        1
    );
    let root = SyntaxNode::new_root(green);
    let body = root
        .descendants()
        .find(|node| node.kind() == SyntaxKind::StringInterpolationBody)
        .expect("interpolation body");
    assert_eq!(body.text().to_string(), "a,b;c\nd\r\ne");
    assert!(root.descendants_with_tokens().any(|element| {
        element.into_token().is_some_and(|token| {
            token.text() == "\n"
                && token
                    .parent()
                    .is_some_and(|parent| parent.kind() == SyntaxKind::StringInterpolation)
        })
    }));
}

#[test]
fn virtual_statement_block_dispatches_declarations_and_expression_without_a_braced_owner() {
    let source = "\"%{role R;,impl T;,cast(x): T;,act A;,value}後\"tail";
    let (green, exit, remainder) = run_virtual_string(source, 0, &plain_fence());
    assert_eq!(exit, StringLiteralExit::Complete);
    assert_eq!(
        green.to_string(),
        "\"%{role R;,impl T;,cast(x): T;,act A;,value}後\""
    );
    assert_eq!(remainder, "tail");
    assert_eq!(count(&green, SyntaxKind::Statement), 5);
    assert_eq!(count(&green, SyntaxKind::RoleDeclaration), 1);
    assert_eq!(count(&green, SyntaxKind::ImplDeclaration), 1);
    assert_eq!(count(&green, SyntaxKind::CastDeclaration), 1);
    assert_eq!(count(&green, SyntaxKind::ActDeclaration), 1);
    assert_eq!(count(&green, SyntaxKind::OperatorChain), 1);
    assert_eq!(count(&green, SyntaxKind::BracedStatementBlockExpression), 0);
    assert_eq!(count(&green, SyntaxKind::Error), 0);
    assert_eq!(count(&green, SyntaxKind::Missing), 0);
}

#[test]
fn virtual_statement_block_recovers_one_malformed_run_and_one_adjacent_separator() {
    let source = "\"%{@ value,x,,y}後\"tail";
    let (green, exit, remainder) = run_virtual_string(source, 0, &plain_fence());
    assert_eq!(exit, StringLiteralExit::Complete);
    assert_eq!(green.to_string(), "\"%{@ value,x,,y}後\"");
    assert_eq!(remainder, "tail");
    assert_eq!(count(&green, SyntaxKind::Statement), 4);
    assert_eq!(count(&green, SyntaxKind::Error), 1);
    assert_eq!(count(&green, SyntaxKind::Missing), 1);
    assert_eq!(count(&green, SyntaxKind::BlockStatementSeparator), 3);
    assert_eq!(
        token_count(&green, SyntaxKind::StringInterpolationCloseBrace),
        1
    );
}

#[test]
fn virtual_statement_block_orders_child_and_parent_recovery_at_eof() {
    let source = "\"%{@";
    let (green, exit, remainder) = run_virtual_string(source, 0, &plain_fence());
    assert!(matches!(exit, StringLiteralExit::Boundary(_)));
    assert_eq!(green.to_string(), source);
    assert_eq!(remainder, "");
    assert_eq!(count(&green, SyntaxKind::Error), 1);
    assert_eq!(count(&green, SyntaxKind::Missing), 2);
    assert_eq!(
        token_count(&green, SyntaxKind::StringInterpolationCloseBrace),
        0
    );
    let root = SyntaxNode::new_root(green);
    let kinds = root
        .descendants_with_tokens()
        .filter(|node| matches!(node.kind(), SyntaxKind::Error | SyntaxKind::Missing))
        .map(|node| node.kind())
        .collect::<Vec<_>>();
    assert_eq!(
        kinds,
        [SyntaxKind::Error, SyntaxKind::Missing, SyntaxKind::Missing]
    );
}

#[test]
fn virtual_statement_block_returns_exact_fence_boundary_origin_and_line_entry() {
    let fence = active_fence();
    let origin = 8100;
    let accepted = "α";
    let source = format!("{accepted}\r\n> > ```\r\nouter");
    let operators = OperatorTable::empty();
    let mut recover = Recover::new_for_test(&operators);
    let mut input = source.as_str();
    let mut builder = GreenNodeBuilder::new();
    builder.start_node(SyntaxKind::Root.into());
    builder.start_node(SyntaxKind::StringInterpolationBody.into());
    let exit = virtual_statement_block_normalized(
        crate::cursor::SyntaxIn::new(&mut input, &mut recover, &mut builder),
        origin,
        LineEntry::InLine,
        Some(&fence),
        None.into(),
    );
    builder.finish_node();
    builder.finish_node();
    let green = finish_without_recoveries(builder, recover);
    let VirtualStatementBlockExit::Boundary(item, LineEntry::PhysicalStart) = exit else {
        panic!("virtual block must return the exact fence boundary")
    };
    let (leading, pending) = emit_terminal_leading_text(item);
    assert_eq!(leading, "\r\n");
    assert_eq!(pending.coordinate(), origin + accepted.len() + 2);
    assert!(matches!(
        pending.into_kind(),
        crate::lexical::item::Boundary::BorrowedClose(
            crate::lexical::item::BorrowedTarget::YumarkFence(_)
        )
    ));
    assert_eq!(green.to_string(), accepted);
    assert_eq!(input, "> > ```\r\nouter");
    assert_eq!(count(&green, SyntaxKind::Statement), 1);
    assert_eq!(count(&green, SyntaxKind::Missing), 0);
    let root = SyntaxNode::new_root(green);
    let body = interpolation_body(&root);
    assert_eq!(
        direct_shape(&body),
        [(SyntaxKind::Statement, 0..accepted.len(), accepted.into())]
    );
    assert_eq!(body.parent(), Some(root));
}

#[test]
fn virtual_string_orders_parent_missing_nodes_before_the_exact_fence_handoff() {
    let source = "\"%{α\r\n> > ```\r\nouter";
    let (green, exit, remainder) = run_virtual_string(source, 9100, &active_fence());
    let StringLiteralExit::Boundary(item) = exit else {
        panic!("the virtual StringLiteral must return its fence boundary")
    };
    let (leading, pending) = emit_terminal_leading_text(item);
    assert_eq!(leading, "\r\n");
    assert!(matches!(
        pending.into_kind(),
        crate::lexical::item::Boundary::BorrowedClose(
            crate::lexical::item::BorrowedTarget::YumarkFence(_)
        )
    ));
    assert_eq!(green.to_string(), "\"%{α");
    assert_eq!(remainder, "> > ```\r\nouter");
    assert_eq!(count(&green, SyntaxKind::Statement), 1);
    assert_eq!(count(&green, SyntaxKind::Error), 0);
    assert_eq!(count(&green, SyntaxKind::Missing), 2);
    assert_eq!(
        token_count(&green, SyntaxKind::StringInterpolationCloseBrace),
        0
    );
}

#[test]
fn virtual_statement_block_resumes_literal_text_after_the_outer_close() {
    let source = "\"前%{value}後%{role R;}末\"tail";
    let (green, exit, remainder) = run_virtual_string(source, 1200, &plain_fence());
    assert_eq!(exit, StringLiteralExit::Complete);
    assert_eq!(green.to_string(), "\"前%{value}後%{role R;}末\"");
    assert_eq!(remainder, "tail");
    assert_eq!(count(&green, SyntaxKind::StringInterpolation), 2);
    assert_eq!(count(&green, SyntaxKind::Statement), 2);
    assert_eq!(count(&green, SyntaxKind::RoleDeclaration), 1);
    assert_eq!(
        token_count(&green, SyntaxKind::StringInterpolationCloseBrace),
        2
    );
    assert_eq!(count(&green, SyntaxKind::Missing), 0);
    assert_eq!(count(&green, SyntaxKind::Error), 0);
}

fn range_of(element: &rowan::NodeOrToken<SyntaxNode, crate::SyntaxToken>) -> Range<usize> {
    usize::from(element.text_range().start())..usize::from(element.text_range().end())
}

fn direct_shape(node: &SyntaxNode) -> Vec<(SyntaxKind, Range<usize>, String)> {
    node.children_with_tokens()
        .map(|element| (element.kind(), range_of(&element), element.to_string()))
        .collect()
}

fn interpolation_body(root: &SyntaxNode) -> SyntaxNode {
    root.descendants()
        .find(|node| node.kind() == SyntaxKind::StringInterpolationBody)
        .expect("StringInterpolationBody")
}

#[test]
fn interpolation_body_cst_distinguishes_statement_and_separator_missing_slots() {
    // Leading and repeated explicit separators require a Statement wrapper;
    // the zero-width Missing belongs to that wrapper, never directly to Body.
    let source = "\"%{,;x,,y}後\"";
    let (green, exit, remainder) = run_virtual_string(source, 0, &plain_fence());
    assert_eq!(exit, StringLiteralExit::Complete);
    assert_eq!(remainder, "");
    let root = SyntaxNode::new_root(green);
    let body = interpolation_body(&root);
    assert_eq!(
        direct_shape(&body),
        [
            (SyntaxKind::Statement, 3..3, "".into()),
            (SyntaxKind::BlockStatementSeparator, 3..4, ",".into()),
            (SyntaxKind::Statement, 4..4, "".into()),
            (SyntaxKind::BlockStatementSeparator, 4..5, ";".into()),
            (SyntaxKind::Statement, 5..6, "x".into()),
            (SyntaxKind::BlockStatementSeparator, 6..7, ",".into()),
            (SyntaxKind::Statement, 7..7, "".into()),
            (SyntaxKind::BlockStatementSeparator, 7..8, ",".into()),
            (SyntaxKind::Statement, 8..9, "y".into()),
        ]
    );
    for statement in body
        .children()
        .filter(|node| node.kind() == SyntaxKind::Statement)
    {
        if statement.text_range().is_empty() {
            let missing = statement.first_child().expect("required Statement Missing");
            assert_eq!(missing.kind(), SyntaxKind::Missing);
            assert_eq!(missing.parent(), Some(statement));
        }
    }
    assert!(
        body.children()
            .all(|node| node.kind() != SyntaxKind::Missing)
    );

    // A declaration-owned semicolon is not a body separator.  Two admitted
    // statements consequently create the distinct direct body separator slot.
    let source = "\"%{role R; value}後\"";
    let (green, exit, remainder) = run_virtual_string(source, 0, &plain_fence());
    assert_eq!(exit, StringLiteralExit::Complete);
    assert_eq!(remainder, "");
    let root = SyntaxNode::new_root(green);
    let body = interpolation_body(&root);
    assert_eq!(
        direct_shape(&body),
        [
            (SyntaxKind::Statement, 3..10, "role R;".into()),
            (SyntaxKind::Missing, 10..10, "".into()),
            (SyntaxKind::Statement, 10..16, " value".into()),
        ]
    );
    let separator_missing = body
        .children()
        .find(|node| node.kind() == SyntaxKind::Missing)
        .expect("direct body separator Missing");
    assert_eq!(separator_missing.parent(), Some(body));

    // A trailing explicit separator terminates at the borrowed close and does
    // not manufacture another required Statement.
    let (green, exit, remainder) = run_virtual_string("\"%{x,}後\"", 0, &plain_fence());
    assert_eq!(exit, StringLiteralExit::Complete);
    assert_eq!(remainder, "");
    let root = SyntaxNode::new_root(green);
    let body = interpolation_body(&root);
    assert_eq!(
        direct_shape(&body),
        [
            (SyntaxKind::Statement, 3..4, "x".into()),
            (SyntaxKind::BlockStatementSeparator, 4..5, ",".into()),
        ]
    );
}

#[test]
fn interpolation_body_cst_owns_error_groups_separators_and_terminal_leading() {
    // Error stops at an ordinary newline.  The newline separator, rather than
    // Error, owns the successor leading before the retried Statement.
    let source = "\"%{@\n x}後\"";
    let (green, exit, remainder) = run_virtual_string(source, 0, &plain_fence());
    assert_eq!(exit, StringLiteralExit::Complete);
    assert_eq!(remainder, "");
    let root = SyntaxNode::new_root(green);
    let body = interpolation_body(&root);
    assert_eq!(
        direct_shape(&body),
        [
            (SyntaxKind::Error, 3..4, "@".into()),
            (SyntaxKind::BlockStatementSeparator, 4..6, "\n ".into()),
            (SyntaxKind::Statement, 6..7, "x".into()),
        ]
    );
    let separator = body
        .children()
        .find(|node| node.kind() == SyntaxKind::BlockStatementSeparator)
        .expect("newline separator");
    assert_eq!(
        direct_shape(&separator),
        [
            (SyntaxKind::Newline, 4..5, "\n".into()),
            (SyntaxKind::Whitespace, 5..6, " ".into()),
        ]
    );

    // Explicit separators absorb their successor leading, but a raw retry is
    // still a direct body Error leaf and never a wrapper node.
    let source = "\"%{x,  @,y}後\"";
    let (green, exit, remainder) = run_virtual_string(source, 0, &plain_fence());
    assert_eq!(exit, StringLiteralExit::Complete);
    assert_eq!(remainder, "");
    let root = SyntaxNode::new_root(green);
    let body = interpolation_body(&root);
    assert_eq!(
        direct_shape(&body),
        [
            (SyntaxKind::Statement, 3..4, "x".into()),
            (SyntaxKind::BlockStatementSeparator, 4..7, ",  ".into()),
            (SyntaxKind::Error, 7..8, "@".into()),
            (SyntaxKind::BlockStatementSeparator, 8..9, ",".into()),
            (SyntaxKind::Statement, 9..10, "y".into()),
        ]
    );
    let explicit = body
        .children()
        .find(|node| node.kind() == SyntaxKind::BlockStatementSeparator)
        .expect("explicit separator");
    assert_eq!(
        direct_shape(&explicit),
        [
            (SyntaxKind::Comma, 4..5, ",".into()),
            (SyntaxKind::Whitespace, 5..7, "  ".into()),
        ]
    );

    // An admitted Statement may retry immediately after Error.  That retry
    // does not invent a body separator Missing, and its leading stays with
    // the Statement rather than being absorbed by the raw Error leaf.
    let source = "\"%{@ role R;}後\"";
    let (green, exit, remainder) = run_virtual_string(source, 0, &plain_fence());
    assert_eq!(exit, StringLiteralExit::Complete);
    assert_eq!(remainder, "");
    let root = SyntaxNode::new_root(green);
    let body = interpolation_body(&root);
    assert_eq!(
        direct_shape(&body),
        [
            (SyntaxKind::Error, 3..4, "@".into()),
            (SyntaxKind::Statement, 4..12, " role R;".into()),
        ]
    );
    assert!(
        body.children()
            .all(|node| node.kind() != SyntaxKind::Missing)
    );
    let retry = body
        .children()
        .find(|node| node.kind() == SyntaxKind::Statement)
        .expect("admitted Statement retry");
    assert_eq!(
        direct_shape(&retry),
        [(SyntaxKind::RoleDeclaration, 4..12, " role R;".into())]
    );

    // UTF-8 and Yumark quote fragments are consecutive physical Error leaves
    // under one body parent; the retry begins only after the comma.
    let source = "\"%{\r\n> > 💥,α}後\"";
    let (green, exit, remainder) = run_virtual_string(source, 0, &active_fence());
    assert_eq!(exit, StringLiteralExit::Complete);
    assert_eq!(remainder, "");
    let root = SyntaxNode::new_root(green);
    let body = interpolation_body(&root);
    assert_eq!(
        direct_shape(&body),
        [
            (SyntaxKind::Error, 3..5, "\r\n".into()),
            (SyntaxKind::Error, 5..9, "> > ".into()),
            (SyntaxKind::Error, 9..13, "💥".into()),
            (SyntaxKind::BlockStatementSeparator, 13..14, ",".into()),
            (SyntaxKind::Statement, 14..16, "α".into()),
        ]
    );
    assert!(
        body.children_with_tokens()
            .filter_map(|element| element.into_token())
            .filter(|token| token.kind() == SyntaxKind::Error)
            .all(|token| token.parent() == Some(body.clone()))
    );

    // Newline immediately before the borrowed close is terminal body leading:
    // it remains an interpolation child, not a newline separator node.
    let (green, exit, remainder) = run_virtual_string("\"%{x\n}後\"", 0, &plain_fence());
    assert_eq!(exit, StringLiteralExit::Complete);
    assert_eq!(remainder, "");
    let root = SyntaxNode::new_root(green);
    let interpolation = root
        .descendants()
        .find(|node| node.kind() == SyntaxKind::StringInterpolation)
        .expect("interpolation");
    assert_eq!(
        direct_shape(&interpolation),
        [
            (SyntaxKind::StringInterpolationPercent, 1..2, "%".into()),
            (SyntaxKind::StringInterpolationOpenBrace, 2..3, "{".into()),
            (SyntaxKind::StringInterpolationBody, 3..4, "x".into()),
            (SyntaxKind::Newline, 4..5, "\n".into()),
            (SyntaxKind::StringInterpolationCloseBrace, 5..6, "}".into()),
        ]
    );
}

#[test]
fn interpolation_body_cst_orders_nested_missing_and_preserves_public_root_text() {
    // The Virtual required Statement, interpolation close and StringLiteral
    // terminator can share offsets.  Their parent paths, not recovery records,
    // distinguish the three slots.
    let source = "\"%{,";
    let (green, exit, remainder) = run_virtual_string(source, 0, &plain_fence());
    assert!(matches!(exit, StringLiteralExit::Boundary(_)));
    assert_eq!(remainder, "");
    let root = SyntaxNode::new_root(green);
    let literal = root.first_child().expect("StringLiteral");
    let interpolation = literal
        .children()
        .find(|node| node.kind() == SyntaxKind::StringInterpolation)
        .expect("interpolation");
    let body = interpolation_body(&root);
    let missing = root
        .descendants()
        .filter(|node| node.kind() == SyntaxKind::Missing)
        .collect::<Vec<_>>();
    assert_eq!(missing.len(), 3);
    assert_eq!(
        missing
            .iter()
            .map(|node| range_of(&node.clone().into()))
            .collect::<Vec<_>>(),
        [3..3, 4..4, 4..4]
    );
    assert_eq!(missing[0].parent().unwrap().kind(), SyntaxKind::Statement);
    assert_eq!(missing[0].parent().unwrap().parent(), Some(body));
    assert_eq!(missing[1].parent(), Some(interpolation));
    assert_eq!(missing[2].parent(), Some(literal));

    // The public parse completes terminal ownership: the direct Rowan Root
    // retains every byte, including interpolation separators and EOF leading.
    for source in ["\"%{@\n x}後\" // tail", "\"%{x\r\ny}後\"\r\n", "\"%{  "] {
        let source: Arc<SourceText> = Arc::from(source);
        let header = Arc::new(scan_header(Arc::clone(&source)));
        let parsed = parse_file(
            Arc::clone(&source),
            header,
            Arc::new(SyntaxEnvironment::empty()),
        );
        assert_eq!(parsed.green().to_string(), source.as_ref());
    }
}
