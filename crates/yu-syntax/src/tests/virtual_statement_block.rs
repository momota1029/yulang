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
                let mut recover = Recover::new(&operators);
                let mut input = source;
                let mut output = frozen
                    .map(GreenNodeBuilder::reconcile)
                    .unwrap_or_else(GreenNodeBuilder::new);
                output.start_node(SyntaxKind::Root.into());
                let exit = virtual_statement_block_normalized(
                    In::new(&mut input, &mut recover, &mut output),
                    origin,
                    LineEntry::InLine,
                    None,
                    None.into(),
                );
                output.finish_node();
                let (green, records) = output.finish_with_recoveries();
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
        let mut recover = Recover::new(&operators);
        let mut input = source;
        let mut output = GreenNodeBuilder::new();
        output.start_node(SyntaxKind::Root.into());
        let exit = virtual_statement_block_normalized(
            In::new(&mut input, &mut recover, &mut output),
            300,
            LineEntry::InLine,
            fence.as_ref(),
            None.into(),
        );
        output.finish_node();
        let (green, records) = output.finish_with_recoveries();
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
        let mut recover = Recover::new(&operators);
        let mut output = GreenNodeBuilder::reconcile(&frozen);
        output.start_node(SyntaxKind::Root.into());
        output.start_node(SyntaxKind::Missing.into());
        output.finish_node();
        output.commit_recovery(crate::cst_output::RecoveryDraft::new(
            seed.site.clone(),
            seed.kind,
            seed.unexpected.clone(),
            seed.expectations.clone(),
            0,
        ));
        for origin in [100, 200] {
            let mut input = source;
            let exit = virtual_statement_block_normalized(
                In::new(&mut input, &mut recover, &mut output),
                origin,
                LineEntry::InLine,
                None,
                None.into(),
            );
            assert!(matches!(exit, VirtualStatementBlockExit::Close(_, _)));
        }
        output.finish_node();
        let (_, records) = output.finish_with_recoveries();
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
        let mut recover = Recover::new(&operators);
        let mut input = "> > @ 💥 α}";
        let mut output = frozen
            .map(GreenNodeBuilder::reconcile)
            .unwrap_or_else(GreenNodeBuilder::new);
        output.start_node(SyntaxKind::Root.into());
        let exit = virtual_statement_block_normalized(
            In::new(&mut input, &mut recover, &mut output),
            400,
            LineEntry::PhysicalStart,
            Some(&fence),
            None.into(),
        );
        output.finish_node();
        let (green, records) = output.finish_with_recoveries();
        assert_eq!(records, expected);
        assert_eq!(green.to_string(), "> > @ 💥 α");
        assert!(matches!(exit, VirtualStatementBlockExit::Close(_, _)));
        assert_eq!(input, "");
    }
}

use crate::{
    lexical::yumark::{FenceOpener, FencePrefixPolicy},
    literal::{
        StringLiteralExit, scan_string_opener_witness,
        string_literal_with_virtual_statements_witness,
    },
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
    let mut recover = Recover::new(&operators);
    let mut input = source;
    let (opener, mode) =
        scan_string_opener_witness(In::new(&mut input, &mut recover, ())).expect("string opener");
    let interior_origin = origin
        .checked_add(opener.payload_view().spelling().expect("opener text").len())
        .expect("literal origin");
    let mut builder = GreenNodeBuilder::new();
    builder.start_node(SyntaxKind::Root.into());
    let exit = string_literal_with_virtual_statements_witness(
        In::new(&mut input, &mut recover, &mut builder),
        opener,
        mode,
        interior_origin,
        fence,
    );
    builder.finish_node();
    (builder.finish_with_recoveries().0, exit, input)
}

fn count(green: &GreenNode, kind: SyntaxKind) -> usize {
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
    let mut recover = Recover::new(&operators);
    let mut input = " \t}tail";
    let mut builder = GreenNodeBuilder::new();
    builder.start_node(SyntaxKind::Root.into());
    let exit = virtual_statement_block_normalized(
        In::new(&mut input, &mut recover, &mut builder),
        400,
        LineEntry::InLine,
        Some(&plain_fence()),
        None.into(),
    );
    builder.finish_node();
    let green = builder.finish();
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
        .descendants()
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
    let mut recover = Recover::new(&operators);
    let mut input = source.as_str();
    let mut builder = GreenNodeBuilder::new();
    builder.start_node(SyntaxKind::Root.into());
    builder.start_node(SyntaxKind::StringInterpolationBody.into());
    let exit = virtual_statement_block_normalized(
        In::new(&mut input, &mut recover, &mut builder),
        origin,
        LineEntry::InLine,
        Some(&fence),
        None.into(),
    );
    builder.finish_node();
    builder.finish_node();
    let green = builder.finish();
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
