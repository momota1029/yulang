use std::collections::BTreeSet;

use chasa_recover::In;

use crate::{
    SyntaxNode,
    grammar::{
        declaration::Recovered,
        expression::{FixedPostfixTail, OperatorChain, OperatorChainItem, PrimaryExpression},
    },
    session::{
        CanonicalRecoveryContinuation, ConstructRole, Delimiter as SessionDelimiter,
        ExpectationSources, ExpectedSyntax, ExpressionRole, GrammarRole, RecoveryKind,
        RecoverySiteKey, SyntaxExpectation,
    },
    syntax_kind::SyntaxKind,
};

use super::{
    driver::{
        Either, ExprMode, PilotContext, borrow_close_for_owner, claim_stop_for_owner, emit_end,
        expr, expr_body, ml_child_after_accept, resume_trivia_boundary, tail, tail_item,
    },
    item::{Boundary, Delimiter, Level, Payload, StopKind, TailKind},
    state::{
        FieldDestination, LegacyParseLocalField, PILOT_FIELD_CONE, PilotFrame, PilotOutput,
        PilotReader, PilotRecoverState, ProvisionalRecovery,
    },
};

struct CompleteRun<'source> {
    green: rowan::GreenNode,
    chain: OperatorChain<'source>,
    scanned: Vec<super::item::ItemIdentity>,
    recovery: PilotRecoverState,
    recoveries: Vec<super::state::PublishedRecovery>,
    remainder: &'source str,
}

fn run_complete(source: &'static str) -> CompleteRun<'static> {
    run_complete_with_frame(source, PilotFrame::default())
}

fn run_complete_with_frame(source: &'static str, frame: PilotFrame) -> CompleteRun<'static> {
    let mut remainder = source;
    let mut recovery = PilotRecoverState::default();
    let mut output = PilotOutput::new(source);
    let exit = expr(
        In::new(&mut remainder, &mut recovery, &mut output),
        PilotContext { root: source },
        Level::OUTER,
        frame,
    )
    .expect("the pilot source has a NUD");
    let Err(Either::Right(end)) = exit else {
        panic!("a complete source must end at an explicit boundary")
    };
    assert!(matches!(
        end.item.payload,
        Payload::Boundary(Boundary::EofAfterTrivia)
    ));
    emit_end(&mut output, &end);
    output.finish_node();
    let chain = output.root_chain().expect("root AST chain").clone();
    let recoveries = output.recoveries().to_vec();
    let green = output.finish_complete();
    CompleteRun {
        green,
        chain,
        scanned: recovery.scanned_items().to_vec(),
        recovery,
        recoveries,
        remainder,
    }
}

fn setup_tail(
    source: &'static str,
) -> (
    &'static str,
    PilotRecoverState,
    PilotOutput<'static>,
    super::item::Item<'static>,
) {
    let mut remainder = source;
    let mut recovery = PilotRecoverState::default();
    let item = tail_item(
        In::new(&mut remainder, &mut recovery, ()),
        PilotContext { root: source },
        PilotFrame::default(),
    )
    .unwrap();
    let mut output = PilotOutput::new(source);
    output.start_node(SyntaxKind::Root);
    output.start_node(SyntaxKind::OperatorChain);
    output.begin_chain(item.extent.start);
    (remainder, recovery, output, item)
}

fn expectation(range: std::ops::Range<usize>) -> SyntaxExpectation {
    SyntaxExpectation {
        role: GrammarRole::Expression(ExpressionRole::Nud),
        expected: ExpectedSyntax::Expression,
        range,
        sources: ExpectationSources::SPECULATIVE,
    }
}

#[test]
fn builds_existing_flat_chain_in_source_order_with_exact_ranges() {
    let run = run_complete("a*b+c");
    assert_eq!(run.remainder, "");
    assert_eq!(run.green.to_string(), "a*b+c");
    assert_eq!(run.chain.range(), 0..5);
    let items = run.chain.items();
    assert_eq!(items.len(), 5);
    assert!(matches!(items[0], OperatorChainItem::Primary(_)));
    let OperatorChainItem::InfixUse(multiply) = &items[1] else {
        panic!()
    };
    assert_eq!(multiply.text(), "*");
    assert_eq!(multiply.range(), 1..2);
    assert!(matches!(items[2], OperatorChainItem::Primary(_)));
    let OperatorChainItem::InfixUse(plus) = &items[3] else {
        panic!()
    };
    assert_eq!(plus.text(), "+");
    assert_eq!(plus.range(), 3..4);
    assert!(matches!(items[4], OperatorChainItem::Primary(_)));
    assert_eq!(
        run.scanned
            .iter()
            .map(|item| item.ordinal)
            .collect::<Vec<_>>(),
        vec![0, 1, 2, 3, 4, 5]
    );
}

#[test]
fn group_ml_and_call_own_nested_operator_chain_cst_and_ast() {
    let group = run_complete("(a)");
    let root = SyntaxNode::new_root(group.green);
    let group_chain = root
        .descendants()
        .filter(|node| node.kind() == SyntaxKind::OperatorChain)
        .find(|node| {
            node.parent()
                .is_some_and(|parent| parent.kind() == SyntaxKind::ParenthesizedExpression)
        })
        .expect("group owns nested OperatorChain");
    assert_eq!(group_chain.text().to_string(), "a");
    let OperatorChainItem::Primary(PrimaryExpression::Parenthesized {
        elements, range, ..
    }) = &group.chain.items()[0]
    else {
        panic!()
    };
    assert_eq!(range, &(0..3));
    assert_eq!(elements[0].range(), 1..2);

    let ml = run_complete("f (a)");
    let root = SyntaxNode::new_root(ml.green);
    let ml_node = root
        .descendants()
        .find(|node| node.kind() == SyntaxKind::MlArgument)
        .unwrap();
    assert!(
        ml_node
            .children()
            .any(|node| node.kind() == SyntaxKind::OperatorChain)
    );
    let whitespace = root
        .descendants_with_tokens()
        .filter_map(|element| element.into_token())
        .find(|token| token.kind() == SyntaxKind::Whitespace)
        .unwrap();
    assert_eq!(
        whitespace.parent().unwrap().kind(),
        SyntaxKind::OperatorChain
    );
    let OperatorChainItem::MlArgument { argument, range } = &ml.chain.items()[1] else {
        panic!()
    };
    assert_eq!(range, &(2..5));
    assert_eq!(argument.range(), 2..5);

    let call = run_complete("f(a)");
    let root = SyntaxNode::new_root(call.green);
    let call_node = root
        .descendants()
        .find(|node| node.kind() == SyntaxKind::CallTail)
        .unwrap();
    assert!(
        call_node
            .children()
            .any(|node| node.kind() == SyntaxKind::OperatorChain)
    );
    let OperatorChainItem::FixedPostfix(FixedPostfixTail::Call(call)) = &call.chain.items()[1]
    else {
        panic!()
    };
    assert_eq!(call.open(), 1..2);
    assert_eq!(call.arguments()[0].range(), 2..3);
    assert_eq!(call.close(), &Recovered::Complete(3..4));
    assert_eq!(call.range(), 1..4);

    let empty = run_complete("f()");
    let OperatorChainItem::FixedPostfix(FixedPostfixTail::Call(call)) = &empty.chain.items()[1]
    else {
        panic!()
    };
    assert!(call.arguments().is_empty());
    assert_eq!(call.close(), &Recovered::Complete(2..3));
}

#[test]
fn binary_prefix_and_ml_each_exercise_normal_item_and_end_handoffs() {
    let (mut remainder, mut recovery, mut output, item) = setup_tail("*b");
    let ok = tail(
        In::new(&mut remainder, &mut recovery, &mut output),
        PilotContext { root: "*b" },
        Level::OUTER,
        ExprMode::MlArgument {
            stop_before_tail: true,
        },
        PilotFrame::default(),
        item,
    );
    assert_eq!(ok, Ok(()), "binary child Ok returns outer scan authority");

    let (mut remainder, mut recovery, mut output, item) = setup_tail("*b+c");
    let left = tail(
        In::new(&mut remainder, &mut recovery, &mut output),
        PilotContext { root: "*b+c" },
        Level(11),
        ExprMode::Normal,
        PilotFrame::default(),
        item,
    );
    let Err(Either::Left(binary_item)) = left else {
        panic!()
    };
    assert_eq!(binary_item.extent, 2..3);
    assert_eq!(
        recovery
            .scanned_items()
            .iter()
            .filter(|id| **id == binary_item.identity)
            .count(),
        1
    );

    let (mut remainder, mut recovery, mut output, item) = setup_tail("*b");
    let end = tail(
        In::new(&mut remainder, &mut recovery, &mut output),
        PilotContext { root: "*b" },
        Level::OUTER,
        ExprMode::Normal,
        PilotFrame::default(),
        item,
    );
    assert!(matches!(end, Err(Either::Right(_))));

    for (source, mode, level, expected) in [
        (
            "-b",
            ExprMode::MlArgument {
                stop_before_tail: true,
            },
            Level::OUTER,
            0,
        ),
        ("-b+c", ExprMode::Normal, Level(11), 1),
        ("-b", ExprMode::Normal, Level::OUTER, 2),
    ] {
        let mut remainder = source;
        let mut recovery = PilotRecoverState::default();
        let mut output = PilotOutput::new(source);
        output.start_node(SyntaxKind::Root);
        output.start_node(SyntaxKind::OperatorChain);
        output.begin_chain(0);
        let exit = expr_body(
            In::new(&mut remainder, &mut recovery, &mut output),
            PilotContext { root: source },
            level,
            mode,
            PilotFrame::default(),
        )
        .unwrap();
        match expected {
            0 => assert_eq!(exit, Ok(())),
            1 => assert!(matches!(exit, Err(Either::Left(_)))),
            _ => assert!(matches!(exit, Err(Either::Right(_)))),
        }
    }

    for (source, mode, level, expected) in [
        (
            " x",
            ExprMode::MlArgument {
                stop_before_tail: true,
            },
            Level::OUTER,
            0,
        ),
        ("x+c", ExprMode::Normal, Level(11), 1),
        ("x", ExprMode::Normal, Level::OUTER, 2),
    ] {
        let (mut remainder, mut recovery, mut output, item) = setup_tail(source);
        let exit = tail(
            In::new(&mut remainder, &mut recovery, &mut output),
            PilotContext { root: source },
            level,
            mode,
            PilotFrame::default(),
            item,
        );
        match expected {
            0 => assert_eq!(exit, Ok(())),
            1 => assert!(matches!(exit, Err(Either::Left(_)))),
            _ => assert!(matches!(exit, Err(Either::Right(_)))),
        }
    }
}

#[test]
fn recovered_operands_keep_child_control_and_handoff_the_same_lower_item() {
    let (mut remainder, mut recovery, mut output, item) = setup_tail("*?+c");
    let binary = tail(
        In::new(&mut remainder, &mut recovery, &mut output),
        PilotContext { root: "*?+c" },
        Level(11),
        ExprMode::Normal,
        PilotFrame::default(),
        item,
    );
    let Err(Either::Left(binary_item)) = binary else {
        panic!()
    };
    assert_eq!(binary_item.extent, 2..3);
    assert_eq!(remainder, "c");
    assert_eq!(
        recovery
            .scanned_items()
            .iter()
            .filter(|identity| **identity == binary_item.identity)
            .count(),
        1
    );

    let source = "-?+c";
    let mut remainder = source;
    let mut recovery = PilotRecoverState::default();
    let mut output = PilotOutput::new(source);
    output.start_node(SyntaxKind::Root);
    output.start_node(SyntaxKind::OperatorChain);
    output.begin_chain(0);
    let prefix = expr_body(
        In::new(&mut remainder, &mut recovery, &mut output),
        PilotContext { root: source },
        Level(11),
        ExprMode::Normal,
        PilotFrame::default(),
    )
    .unwrap();
    let Err(Either::Left(prefix_item)) = prefix else {
        panic!()
    };
    assert_eq!(prefix_item.extent, 2..3);
    assert_eq!(remainder, "c");
    assert_eq!(
        recovery
            .scanned_items()
            .iter()
            .filter(|identity| **identity == prefix_item.identity)
            .count(),
        1
    );

    let (mut remainder, mut recovery, mut output, item) = setup_tail(" -?+c");
    let Some(TailKind::MlNud(nud_kind)) = item.tail_kind() else {
        panic!()
    };
    let (ml_child, argument) = ml_child_after_accept(
        In::new(&mut remainder, &mut recovery, &mut output),
        PilotContext { root: " -?+c" },
        Level(11),
        PilotFrame::default(),
        &item,
        nud_kind,
    );
    assert_eq!(ml_child, Ok(()));
    assert_eq!(remainder, "+c");
    assert!(matches!(
        argument.items(),
        [OperatorChainItem::PrefixUse(_), OperatorChainItem::Error { range }]
            if range == &(2..3)
    ));
    assert_eq!(
        recovery
            .scanned_items()
            .iter()
            .map(|identity| identity.ordinal)
            .collect::<Vec<_>>(),
        vec![0, 1]
    );
}

#[test]
fn malformed_accepted_owners_publish_typed_total_recoveries() {
    let cases = [
        (
            "a+",
            GrammarRole::Expression(ExpressionRole::Nud),
            RecoveryKind::Missing,
            CanonicalRecoveryContinuation::StopAtBoundary,
        ),
        (
            "-?",
            GrammarRole::Expression(ExpressionRole::Nud),
            RecoveryKind::Error,
            CanonicalRecoveryContinuation::RetrySameSlot,
        ),
        (
            "f ?",
            GrammarRole::Expression(ExpressionRole::MlArgument),
            RecoveryKind::Error,
            CanonicalRecoveryContinuation::RetrySameSlot,
        ),
        (
            "(?)",
            GrammarRole::Expression(ExpressionRole::Nud),
            RecoveryKind::Error,
            CanonicalRecoveryContinuation::RetrySameSlot,
        ),
        (
            "f(?)",
            GrammarRole::Expression(ExpressionRole::CallArgument),
            RecoveryKind::Error,
            CanonicalRecoveryContinuation::RetrySameSlot,
        ),
        (
            "f(a",
            GrammarRole::ClosingDelimiter {
                owner: ConstructRole::ArgumentList,
                delimiter: SessionDelimiter::Parenthesis,
            },
            RecoveryKind::Missing,
            CanonicalRecoveryContinuation::StopAtBoundary,
        ),
    ];
    for (source, role, kind, continuation) in cases {
        let run = run_complete(source);
        assert_eq!(run.recoveries.len(), 1, "{source}");
        let recovery = &run.recoveries[0];
        assert_eq!(recovery.record.site.role, role, "{source}");
        assert_eq!(recovery.record.kind, kind, "{source}");
        assert_eq!(
            recovery.record.expectations[0].sources,
            ExpectationSources::COMMITTED_RECOVERY_RULE,
            "{source}"
        );
        assert_eq!(recovery.continuation, continuation, "{source}");
        let root = SyntaxNode::new_root(run.green.clone());
        assert!(
            root.descendants().any(|node| node.kind()
                == if kind == RecoveryKind::Missing {
                    SyntaxKind::Missing
                } else {
                    SyntaxKind::Error
                }),
            "{source}"
        );
        assert!(
            run.chain.items().iter().any(|item| matches!(
                item,
                OperatorChainItem::MissingOperand { .. } | OperatorChainItem::Error { .. }
            )) || source.starts_with('f')
                || source.starts_with('('),
            "{source}"
        );
        if source == "f ?" {
            let OperatorChainItem::MlArgument { argument, .. } = &run.chain.items()[1] else {
                panic!()
            };
            assert!(
                matches!(argument.items(), [OperatorChainItem::Error { range }] if range == &(2..3))
            );
            let root = SyntaxNode::new_root(run.green.clone());
            let error = root
                .descendants()
                .find(|node| node.kind() == SyntaxKind::Error)
                .unwrap();
            assert_eq!(error.parent().unwrap().kind(), SyntaxKind::OperatorChain);
            assert_eq!(
                error.parent().unwrap().parent().unwrap().kind(),
                SyntaxKind::MlArgument
            );
        }
        if source == "f(a" {
            assert_eq!(
                run.chain.items().len(),
                2,
                "a missing close is not an expression operand"
            );
        }
    }
}

#[test]
fn paren_layout_controls_and_boundary_resumption_preserve_same_item() {
    let call = run_complete("f()");
    assert!(matches!(
        call.chain.items()[1],
        OperatorChainItem::FixedPostfix(FixedPostfixTail::Call(_))
    ));
    let ml = run_complete("f (a)");
    assert!(matches!(
        ml.chain.items()[1],
        OperatorChainItem::MlArgument { .. }
    ));

    let source = "f\r\n(a)";
    let mut remainder = source;
    let mut recovery = PilotRecoverState::default();
    let mut output = PilotOutput::new(source);
    let exit = expr(
        In::new(&mut remainder, &mut recovery, &mut output),
        PilotContext { root: source },
        Level::OUTER,
        PilotFrame::default(),
    )
    .unwrap();
    let Err(Either::Right(end)) = exit else {
        panic!()
    };
    assert!(matches!(
        end.item.payload,
        Payload::Boundary(Boundary::Dedent(_))
    ));
    assert_eq!(end.item.leading_trivia.text, "\r\n");
    assert_eq!(end.item.extent, 1..3);
    assert_eq!(end.item.logical_position.line, 1);
    assert_eq!(end.item.logical_position.column, 0);
    assert_eq!(remainder, "(a)");
    let identity = end.item.identity;
    let still_dedent = resume_trivia_boundary(
        In::new(&mut remainder, &mut recovery, ()),
        PilotContext { root: source },
        PilotFrame {
            layout_baseline: 1,
            allow_same_level_newline: true,
            ..PilotFrame::default()
        },
        end.item.clone(),
    );
    assert_eq!(still_dedent, end.item);
    assert_eq!(remainder, "(a)");

    let mut wrong_remainder = &remainder[1..];
    let wrong_cursor = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        resume_trivia_boundary(
            In::new(&mut wrong_remainder, &mut recovery, ()),
            PilotContext { root: source },
            PilotFrame {
                allow_same_level_newline: true,
                ..PilotFrame::default()
            },
            end.item.clone(),
        )
    }));
    assert!(wrong_cursor.is_err());
    assert_eq!(wrong_remainder, "a)");

    let resumed = resume_trivia_boundary(
        In::new(&mut remainder, &mut recovery, ()),
        PilotContext { root: source },
        PilotFrame {
            allow_same_level_newline: true,
            ..PilotFrame::default()
        },
        end.item,
    );
    assert_eq!(resumed.identity, identity);
    assert_eq!(resumed.leading_trivia.text, "\r\n");
    assert_eq!(resumed.extent, 1..4);
    assert_eq!(resumed.logical_position.line, 1);
    assert!(matches!(
        resumed.payload,
        Payload::Tail {
            kind: TailKind::MlNud(_),
            ..
        }
    ));
    assert_eq!(
        recovery
            .scanned_items()
            .iter()
            .filter(|id| **id == identity)
            .count(),
        1
    );
}

#[test]
fn eof_trivia_boundary_resume_changes_only_the_same_item_payload() {
    let source = "a\n";
    let mut remainder = source;
    let mut recovery = PilotRecoverState::default();
    let mut output = PilotOutput::new(source);
    let exit = expr(
        In::new(&mut remainder, &mut recovery, &mut output),
        PilotContext { root: source },
        Level::OUTER,
        PilotFrame::default(),
    )
    .unwrap();
    let Err(Either::Right(end)) = exit else {
        panic!()
    };
    assert!(matches!(
        end.item.payload,
        Payload::Boundary(Boundary::Dedent(_))
    ));
    assert_eq!(remainder, "");
    let scanned = recovery.scanned_items().to_vec();
    let mut expected = end.item.clone();
    expected.payload = Payload::Boundary(Boundary::EofAfterTrivia);

    let resumed = resume_trivia_boundary(
        In::new(&mut remainder, &mut recovery, ()),
        PilotContext { root: source },
        PilotFrame {
            allow_same_level_newline: true,
            ..PilotFrame::default()
        },
        end.item,
    );

    assert_eq!(resumed, expected);
    assert_eq!(remainder, "");
    assert_eq!(recovery.scanned_items(), scanned);
}

#[test]
fn close_stop_and_eof_retain_identity_trivia_extent_and_logical_position() {
    let source = " \t)tail";
    let mut remainder = source;
    let mut recovery = PilotRecoverState::default();
    let close = tail_item(
        In::new(&mut remainder, &mut recovery, ()),
        PilotContext { root: source },
        PilotFrame::default(),
    )
    .unwrap();
    let identity = close.identity;
    assert_eq!(close.logical_position.line, 0);
    assert_eq!(close.logical_position.column, 2);
    let wrong_close_owner = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        borrow_close_for_owner(close.clone(), PilotFrame::default())
    }));
    assert!(wrong_close_owner.is_err());
    let borrowed = borrow_close_for_owner(
        close,
        PilotFrame {
            delimiter: Some(Delimiter::Parenthesis),
            ..PilotFrame::default()
        },
    );
    assert_eq!(borrowed.identity, identity);
    assert_eq!(borrowed.extent, 0..3);
    assert!(matches!(
        borrowed.payload,
        Payload::Boundary(Boundary::BorrowedClose(Delimiter::Parenthesis))
    ));

    let source = " ,tail";
    let mut remainder = source;
    let mut recovery = PilotRecoverState::default();
    let token = tail_item(
        In::new(&mut remainder, &mut recovery, ()),
        PilotContext { root: source },
        PilotFrame::default(),
    )
    .unwrap();
    let wrong_stop_token = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        claim_stop_for_owner(
            token.clone(),
            PilotFrame {
                stop: Some(StopKind::Semicolon),
                ..PilotFrame::default()
            },
            StopKind::Semicolon,
        )
    }));
    assert!(wrong_stop_token.is_err());
    let wrong_stop_owner = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        claim_stop_for_owner(token.clone(), PilotFrame::default(), StopKind::Comma)
    }));
    assert!(wrong_stop_owner.is_err());
    let stop = claim_stop_for_owner(
        token,
        PilotFrame {
            stop: Some(StopKind::Comma),
            ..PilotFrame::default()
        },
        StopKind::Comma,
    );
    assert_eq!(stop.leading_trivia.text, " ");
    assert_eq!(stop.logical_position.column, 1);
    assert!(matches!(
        stop.payload,
        Payload::Boundary(Boundary::Stop(StopKind::Comma))
    ));

    let eof = run_complete_with_frame(
        "α\r\n",
        PilotFrame {
            allow_same_level_newline: true,
            ..PilotFrame::default()
        },
    );
    assert_eq!(eof.remainder, "");
    assert_eq!(eof.recovery.line.last_newline, Some((2, 4)));
    assert_eq!(eof.recovery.line.line_number, 1);
    assert_eq!(eof.recovery.line.column, 0);
}

#[test]
fn unread_tail_preserves_complete_input_r_frame_s_and_item_snapshot() {
    let source = "  +x";
    let context = PilotContext { root: source };
    let frame = PilotFrame {
        layout_baseline: 3,
        allow_same_level_newline: true,
        delimiter: Some(Delimiter::Brace),
        ..PilotFrame::default()
    };
    let mut remainder = source;
    let mut recovery = PilotRecoverState::default();
    let item = tail_item(In::new(&mut remainder, &mut recovery, ()), context, frame).unwrap();
    recovery.line.line_start = 7;
    recovery.record_expectation(expectation(3..3));
    let _ = recovery.allocate_diagnostic_id();
    recovery.record_provisional_recovery(ProvisionalRecovery {
        site: RecoverySiteKey {
            role: GrammarRole::Expression(ExpressionRole::Nud),
            range: 3..3,
        },
        kind: RecoveryKind::Missing,
    });
    recovery.is_cut = true;
    let expected_scans = recovery.scanned_items().to_vec();
    let expected_item = item.clone();
    let mut output = PilotOutput::new(source);
    let exit = tail(
        In::new(&mut remainder, &mut recovery, &mut output),
        context,
        Level(11),
        ExprMode::Normal,
        frame,
        item,
    );
    let Err(Either::Left(returned)) = exit else {
        panic!()
    };
    assert_eq!(returned, expected_item);
    assert_eq!(returned.identity.ordinal, 0);
    assert_eq!(returned.leading_trivia.text, "  ");
    assert_eq!(returned.logical_position.column, 2);
    assert_eq!(remainder, "x");
    assert_eq!(recovery.line.line_start, 7);
    assert_eq!(recovery.expectations(), &[expectation(3..3)]);
    assert_eq!(recovery.next_diagnostic_id(), 1);
    assert_eq!(recovery.provisional_recoveries().len(), 1);
    assert!(recovery.is_cut);
    assert_eq!(recovery.scanned_items(), expected_scans);
    assert_eq!(frame.delimiter, Some(Delimiter::Brace));
    assert!(output.root_chain().is_none());
    assert!(output.recoveries().is_empty());
}

#[test]
fn pilot_field_cone_is_exhaustive_and_recovery_reuse_stays_at_gate_seven() {
    let fields = PILOT_FIELD_CONE
        .iter()
        .map(|entry| entry.field)
        .collect::<BTreeSet<_>>();
    assert_eq!(fields.len(), 23);
    assert_eq!(fields.len(), PILOT_FIELD_CONE.len());
    let line = PILOT_FIELD_CONE
        .iter()
        .find(|entry| entry.field == LegacyParseLocalField::Line)
        .unwrap();
    assert_eq!(line.destination, FieldDestination::RecoverableState);
    assert_eq!(line.reader, Some(PilotReader::TriviaScanner));
    for field in [
        LegacyParseLocalField::ReusableRecoveries,
        LegacyParseLocalField::ReusedRecoveryIndices,
    ] {
        let entry = PILOT_FIELD_CONE
            .iter()
            .find(|entry| entry.field == field)
            .unwrap();
        assert_eq!(entry.destination, FieldDestination::NoPilotReader);
        assert_eq!(entry.reader, None);
        assert_eq!(entry.retained_gate, Some(7));
    }
}

#[test]
fn effect_free_entry_nonmatch_preserves_input_r_and_output() {
    let source = ")";
    let mut remainder = source;
    let mut recovery = PilotRecoverState::default();
    recovery.line.line_start = 4;
    let mut output = PilotOutput::new(source);
    let result = expr(
        In::new(&mut remainder, &mut recovery, &mut output),
        PilotContext { root: source },
        Level::OUTER,
        PilotFrame::default(),
    );
    assert_eq!(result, None);
    assert_eq!(remainder, source);
    assert_eq!(recovery.line.line_start, 4);
    assert_eq!(recovery.next_item_ordinal, 0);
    assert!(recovery.scanned_items().is_empty());
    assert!(output.root_chain().is_none());
    assert!(output.recoveries().is_empty());
}
