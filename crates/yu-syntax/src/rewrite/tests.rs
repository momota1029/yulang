use std::{collections::BTreeSet, sync::Arc};

use chasa_recover::In;

use crate::{
    SyntaxNode,
    grammar::{
        declaration::Recovered,
        expression::{
            FixedPostfixTail, OperatorChain, OperatorChainItem, PathSegment, PrimaryExpression,
        },
    },
    session::{
        CanonicalRecoveryContinuation, ConstructRole, Delimiter as SessionDelimiter, DiagnosticId,
        ExpectationSources, ExpectedSyntax, ExpressionRole, GrammarRole, RecoveryKind,
        RecoverySiteKey, SyntaxExpectation,
    },
    syntax_kind::SyntaxKind,
};

use super::{
    driver::{
        BorrowedArgsOwner, Either, ExprMode, PilotContext, borrow_close_for_owner,
        claim_stop_for_owner, emit_end, expr, expr_body, ml_child_after_accept,
        present_borrowed_args, resume_trivia_boundary, tail, tail_item,
    },
    item::{Boundary, Delimiter, Level, Payload, StopKind, TailKind},
    state::{
        FieldDestination, LegacyParseLocalField, PILOT_FIELD_CONE, PersistentRecovery, PilotFrame,
        PilotOutput, PilotReader, PilotRecoverState, ProvisionalRecovery, RecoveryChainItem,
        RecoveryDraft,
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
fn gate3_field_and_path_tails_build_flat_ast_and_direct_cst_in_source_order() {
    let run = run_complete("x.foo::bar::baz");
    assert_eq!(run.remainder, "");
    assert_eq!(run.green.to_string(), "x.foo::bar::baz");
    assert_eq!(run.chain.range(), 0..15);
    let [
        OperatorChainItem::Primary(PrimaryExpression::Identifier(x)),
        OperatorChainItem::FixedPostfix(FixedPostfixTail::Field(field)),
        OperatorChainItem::FixedPostfix(FixedPostfixTail::Path(bar)),
        OperatorChainItem::FixedPostfix(FixedPostfixTail::Path(baz)),
    ] = run.chain.items()
    else {
        panic!("Gate 3 fixed tails remain flat source-order chain items")
    };
    assert_eq!(x.text(), "x");
    assert_eq!(field.dot(), 1..2);
    assert!(matches!(field.name(), Recovered::Complete(name) if name.text() == "foo"));
    assert_eq!(field.range(), 1..5);
    assert_eq!(bar.separator(), 5..7);
    assert!(
        matches!(bar.segment(), Recovered::Complete(PathSegment::Identifier(name)) if name.text() == "bar")
    );
    assert_eq!(bar.range(), 5..10);
    assert_eq!(baz.separator(), 10..12);
    assert!(
        matches!(baz.segment(), Recovered::Complete(PathSegment::Identifier(name)) if name.text() == "baz")
    );
    assert_eq!(baz.range(), 10..15);

    let root = SyntaxNode::new_root(run.green);
    let chain = root
        .children()
        .find(|node| node.kind() == SyntaxKind::OperatorChain)
        .unwrap();
    assert_eq!(
        chain.children().map(|node| node.kind()).collect::<Vec<_>>(),
        vec![
            SyntaxKind::IdentifierExpression,
            SyntaxKind::FieldTail,
            SyntaxKind::PathTail,
            SyntaxKind::PathTail,
        ]
    );
    assert_eq!(
        run.scanned
            .iter()
            .map(|identity| identity.ordinal)
            .collect::<Vec<_>>(),
        vec![0, 1, 2, 3, 4],
        "accepted fixed tails scan their successor once"
    );
}

#[test]
fn gate3_spaced_sigil_path_keeps_trivia_inside_the_path_owner() {
    let run = run_complete("x:: $name");
    let [
        OperatorChainItem::Primary(_),
        OperatorChainItem::FixedPostfix(FixedPostfixTail::Path(path)),
    ] = run.chain.items()
    else {
        panic!()
    };
    assert_eq!(path.separator(), 1..3);
    assert!(matches!(
        path.segment(),
        Recovered::Complete(PathSegment::SigilIdentifier(name))
            if name.text() == "$name" && name.range() == (4..9)
    ));
    assert_eq!(path.range(), 1..9);
    let root = SyntaxNode::new_root(run.green);
    let path = root
        .descendants()
        .find(|node| node.kind() == SyntaxKind::PathTail)
        .unwrap();
    assert_eq!(
        path.children_with_tokens()
            .map(|element| {
                (
                    element.kind(),
                    usize::from(element.text_range().start())
                        ..usize::from(element.text_range().end()),
                )
            })
            .collect::<Vec<_>>(),
        vec![
            (SyntaxKind::ColonColon, 1..3),
            (SyntaxKind::Whitespace, 3..4),
            (SyntaxKind::SigilIdentifier, 4..9),
        ]
    );
}

#[test]
fn gate3_fixed_tail_recovery_is_typed_local_and_retries_the_same_slot() {
    for (source, role, kind, range) in [
        ("x.", ExpressionRole::FieldName, RecoveryKind::Missing, 2..2),
        ("x.@", ExpressionRole::FieldName, RecoveryKind::Error, 2..3),
        (
            "x::",
            ExpressionRole::PathSegment,
            RecoveryKind::Missing,
            3..3,
        ),
        (
            "x::123",
            ExpressionRole::PathSegment,
            RecoveryKind::Error,
            3..6,
        ),
    ] {
        let run = run_complete(source);
        let [recovery] = run.recoveries.as_slice() else {
            panic!("one owner-local fixed-tail recovery for {source:?}")
        };
        assert_eq!(recovery.record.id.0, 0, "{source:?}");
        assert_eq!(recovery.record.site.role, GrammarRole::Expression(role));
        assert_eq!(recovery.record.site.range, range);
        assert_eq!(recovery.record.kind, kind);
        assert_eq!(
            recovery.record.expectations[recovery.record.primary_expectation].expected,
            ExpectedSyntax::Identifier
        );
        assert_eq!(
            recovery.continuation,
            if kind == RecoveryKind::Missing {
                CanonicalRecoveryContinuation::StopAtBoundary
            } else {
                CanonicalRecoveryContinuation::RetrySameSlot
            }
        );
        assert!(
            !run.chain.items().iter().any(|item| matches!(
                item,
                OperatorChainItem::MissingOperand { .. } | OperatorChainItem::Error { .. }
            )),
            "fixed-tail recovery does not escape into the top-level chain: {source:?}"
        );
        let root = SyntaxNode::new_root(run.green);
        let recovery_node = root
            .descendants()
            .find(|node| {
                node.kind()
                    == if kind == RecoveryKind::Missing {
                        SyntaxKind::Missing
                    } else {
                        SyntaxKind::Error
                    }
            })
            .unwrap();
        assert_eq!(
            recovery_node.parent().unwrap().kind(),
            if role == ExpressionRole::FieldName {
                SyntaxKind::FieldTail
            } else {
                SyntaxKind::PathTail
            }
        );
    }

    let retry = run_complete("x::::$name");
    let [
        OperatorChainItem::Primary(_),
        OperatorChainItem::FixedPostfix(FixedPostfixTail::Path(first)),
        OperatorChainItem::FixedPostfix(FixedPostfixTail::Path(second)),
    ] = retry.chain.items()
    else {
        panic!("the retained second separator retries the same Path slot")
    };
    assert_eq!(first.separator(), 1..3);
    assert_eq!(first.segment(), &Recovered::Incomplete);
    assert_eq!(second.separator(), 3..5);
    assert!(matches!(
        second.segment(),
        Recovered::Complete(PathSegment::SigilIdentifier(name)) if name.text() == "$name"
    ));
    assert_eq!(retry.recoveries[0].record.site.range, 3..3);
    assert_eq!(
        retry
            .scanned
            .iter()
            .map(|identity| identity.ordinal)
            .collect::<Vec<_>>(),
        vec![0, 1, 2, 3]
    );
}

#[test]
fn gate3_dot_family_defer_returns_the_exact_item_without_publication() {
    for source in [".(", ".{", ".."] {
        let (mut remainder, mut recovery, mut output, item) = setup_tail(source);
        assert_eq!(item.tail_kind(), Some(TailKind::Deferred));
        assert_eq!(item.extent, 0..1);
        assert_eq!(remainder, &source[1..]);

        recovery.line.last_newline = Some((11, 13));
        recovery.line.line_start = 13;
        recovery.line.line_indent = 17;
        recovery.line.line_number = 19;
        recovery.line.column = 23;
        recovery.line.at_line_start = true;
        recovery.record_expectation(expectation(1..1));
        let _ = recovery.allocate_diagnostic_id();
        recovery.record_provisional_recovery(ProvisionalRecovery {
            site: RecoverySiteKey {
                role: GrammarRole::Expression(ExpressionRole::Nud),
                range: 1..1,
            },
            kind: RecoveryKind::Missing,
        });
        recovery.record_persistent_recovery(PersistentRecovery {
            site: RecoverySiteKey {
                role: GrammarRole::Expression(ExpressionRole::MlArgument),
                range: 0..1,
            },
            kind: RecoveryKind::Error,
        });
        recovery.is_cut = true;

        let frame = PilotFrame {
            layout_baseline: 29,
            allow_same_level_newline: true,
            delimiter: Some(Delimiter::Brace),
            stop: Some(StopKind::Semicolon),
        };
        let expected_remainder = remainder;
        let expected_remainder_pointer = remainder.as_ptr();
        let expected_cursor = source.len() - remainder.len();
        let expected_item = item.clone();
        let expected_line = recovery.line;
        let expected_next_item_ordinal = recovery.next_item_ordinal;
        let expected_scans = recovery.scanned_items().to_vec();
        let expected_expectations = recovery.expectations().to_vec();
        let expected_next_diagnostic_id = recovery.next_diagnostic_id();
        let expected_provisional = recovery.provisional_recoveries().to_vec();
        let expected_persistent = recovery.persistent_recoveries().to_vec();
        let expected_is_cut = recovery.is_cut;
        let expected_frame = frame;

        let committed_expectation = SyntaxExpectation {
            role: GrammarRole::Expression(ExpressionRole::Nud),
            expected: ExpectedSyntax::Expression,
            range: 0..0,
            sources: ExpectationSources::COMMITTED_RECOVERY_RULE,
        };
        output.publish_recovery(
            DiagnosticId(41),
            RecoveryDraft {
                site: RecoverySiteKey {
                    role: committed_expectation.role,
                    range: committed_expectation.range.clone(),
                },
                kind: RecoveryKind::Missing,
                unexpected: Arc::from([]),
                expectations: Arc::from([committed_expectation]),
                primary_expectation: 0,
                continuation: CanonicalRecoveryContinuation::StopAtBoundary,
            },
            0..0,
            RecoveryChainItem::MissingOperand,
        );
        let expected_committed_recoveries = output.recoveries().to_vec();

        let exit = tail(
            In::new(&mut remainder, &mut recovery, &mut output),
            PilotContext { root: source },
            Level::OUTER,
            ExprMode::Normal,
            frame,
            item,
        );
        let Err(Either::Left(returned)) = exit else {
            panic!("deferred dot stays caller-owned: {source:?}")
        };
        assert_eq!(returned, expected_item);
        assert_eq!(remainder, expected_remainder);
        assert_eq!(remainder.as_ptr(), expected_remainder_pointer);
        assert_eq!(source.len() - remainder.len(), expected_cursor);
        assert_eq!(recovery.line, expected_line);
        assert_eq!(recovery.next_item_ordinal, expected_next_item_ordinal);
        assert_eq!(recovery.scanned_items(), expected_scans);
        assert_eq!(recovery.expectations(), expected_expectations);
        assert_eq!(recovery.next_diagnostic_id(), expected_next_diagnostic_id);
        assert_eq!(recovery.provisional_recoveries(), expected_provisional);
        assert_eq!(recovery.persistent_recoveries(), expected_persistent);
        assert_eq!(recovery.is_cut, expected_is_cut);
        assert_eq!(frame, expected_frame);
        assert_eq!(output.recoveries(), expected_committed_recoveries);
        assert!(output.root_chain().is_none());

        let unchanged_chain = output.finish_chain();
        assert!(matches!(
            unchanged_chain.items(),
            [OperatorChainItem::MissingOperand { range }] if range == &(0..0)
        ));
        output.finish_node();
        output.finish_node();
        let root = SyntaxNode::new_root(output.finish_prefix());
        assert_eq!(root.to_string(), "");
        let chain = root
            .children()
            .find(|node| node.kind() == SyntaxKind::OperatorChain)
            .unwrap();
        assert_eq!(
            chain.children().map(|node| node.kind()).collect::<Vec<_>>(),
            vec![SyntaxKind::Missing]
        );
    }
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
fn gate3_ml_argument_owns_its_adjacent_fixed_tail_chain() {
    let run = run_complete("f x.field(y)::z");
    let [
        OperatorChainItem::Primary(PrimaryExpression::Identifier(function)),
        OperatorChainItem::MlArgument { argument, range },
    ] = run.chain.items()
    else {
        panic!("the adjacent fixed-tail chain belongs to the ML argument")
    };
    assert_eq!(function.text(), "f");
    assert_eq!(range, &(2..15));
    let [
        OperatorChainItem::Primary(PrimaryExpression::Identifier(argument_name)),
        OperatorChainItem::FixedPostfix(FixedPostfixTail::Field(field)),
        OperatorChainItem::FixedPostfix(FixedPostfixTail::Call(call)),
        OperatorChainItem::FixedPostfix(FixedPostfixTail::Path(path)),
    ] = argument.items()
    else {
        panic!("Field, Call, and Path remain inside the nested argument chain")
    };
    assert_eq!(argument_name.text(), "x");
    assert!(matches!(field.name(), Recovered::Complete(name) if name.text() == "field"));
    assert_eq!(call.arguments()[0].range(), 10..11);
    assert_eq!(call.close(), &Recovered::Complete(11..12));
    assert!(matches!(
        path.segment(),
        Recovered::Complete(PathSegment::Identifier(name)) if name.text() == "z"
    ));

    let root = SyntaxNode::new_root(run.green);
    let ml_argument = root
        .descendants()
        .find(|node| node.kind() == SyntaxKind::MlArgument)
        .unwrap();
    let nested_chain = ml_argument
        .children()
        .find(|node| node.kind() == SyntaxKind::OperatorChain)
        .unwrap();
    assert_eq!(nested_chain.text().to_string(), "x.field(y)::z");
    assert_eq!(
        nested_chain
            .children()
            .map(|node| node.kind())
            .collect::<Vec<_>>(),
        vec![
            SyntaxKind::IdentifierExpression,
            SyntaxKind::FieldTail,
            SyntaxKind::CallTail,
            SyntaxKind::PathTail,
        ]
    );
    let nested_call = nested_chain
        .children()
        .find(|node| node.kind() == SyntaxKind::CallTail)
        .unwrap();
    assert!(
        nested_call
            .children()
            .any(|node| node.kind() == SyntaxKind::OperatorChain)
    );

    let source = " x .field";
    let (mut remainder, mut recovery, mut output, item) = setup_tail(source);
    let Some(TailKind::MlNud(nud_kind)) = item.tail_kind() else {
        panic!()
    };
    let (exit, argument) = ml_child_after_accept(
        In::new(&mut remainder, &mut recovery, &mut output),
        PilotContext { root: source },
        Level::OUTER,
        PilotFrame::default(),
        &item,
        nud_kind,
    );
    assert_eq!(exit, Ok(()));
    assert_eq!(remainder, " .field");
    assert!(matches!(
        argument.items(),
        [OperatorChainItem::Primary(PrimaryExpression::Identifier(name))]
            if name.text() == "x"
    ));
    assert_eq!(
        recovery
            .scanned_items()
            .iter()
            .map(|identity| identity.ordinal)
            .collect::<Vec<_>>(),
        vec![0]
    );
}

#[test]
fn gate3_present_borrowed_close_is_emitted_only_by_each_args_owner() {
    for (source, owner, open, close, args_kind) in [
        (
            "\\ref(x. )tail",
            BorrowedArgsOwner::InlineReference,
            4..5,
            8..9,
            SyntaxKind::YmYulangArgs,
        ),
        (
            "[d]:f(x. )tail",
            BorrowedArgsOwner::InlineApply,
            5..6,
            9..10,
            SyntaxKind::YmInlineApplyArgs,
        ),
    ] {
        let mut remainder = &source[open.end..];
        let mut recovery = PilotRecoverState::default();
        recovery.line.column = open.end;
        recovery.line.at_line_start = false;
        let mut output = PilotOutput::new(source);
        output.start_node(SyntaxKind::Root);
        output.token_range(SyntaxKind::Unknown, 0..open.start);
        let result = present_borrowed_args(
            In::new(&mut remainder, &mut recovery, &mut output),
            PilotContext { root: source },
            owner,
            open.clone(),
            PilotFrame::default(),
        )
        .expect("the Gate 3 witness has a qualifying leading-space close");
        output.finish_node();

        assert_eq!(remainder, "tail", "{source:?}");
        assert_eq!(result.range, open.start..close.end);
        assert_eq!(result.close_item.identity.ordinal, 2);
        assert_eq!(result.close_item.leading_trivia.text, " ");
        assert_eq!(result.close_item.extent, (close.start - 1)..close.end);
        assert_eq!(result.close_item.logical_position.line, 0);
        assert_eq!(result.close_item.logical_position.column, close.start);
        assert!(matches!(
            result.close_item.payload,
            Payload::Boundary(Boundary::BorrowedClose(Delimiter::Parenthesis))
        ));
        assert_eq!(
            result
                .close_item
                .lexical_boundary_token
                .as_ref()
                .unwrap()
                .lexeme
                .range,
            close
        );
        assert!(matches!(
            result.expression.items(),
            [
                OperatorChainItem::Primary(PrimaryExpression::Identifier(name)),
                OperatorChainItem::FixedPostfix(FixedPostfixTail::Field(field)),
            ] if name.text() == "x"
                && field.dot() == (open.end + 1..open.end + 2)
                && field.name() == &Recovered::Incomplete
        ));
        let [published] = output.recoveries() else {
            panic!("one FieldName recovery belongs to the child expression")
        };
        assert_eq!(published.record.id.0, 0);
        assert_eq!(
            published.record.site.role,
            GrammarRole::Expression(ExpressionRole::FieldName)
        );
        assert_eq!(
            published.record.site.range,
            close.start - 1..close.start - 1
        );
        assert_eq!(published.record.kind, RecoveryKind::Missing);
        assert_eq!(
            published.continuation,
            CanonicalRecoveryContinuation::StopAtBoundary
        );
        assert_eq!(
            recovery
                .scanned_items()
                .iter()
                .map(|identity| identity.ordinal)
                .collect::<Vec<_>>(),
            vec![0, 1, 2],
            "the returned close item is not rescanned"
        );

        let root = SyntaxNode::new_root(output.finish_prefix());
        assert_eq!(root.to_string(), &source[..close.end]);
        let args = root
            .descendants()
            .find(|node| node.kind() == args_kind)
            .unwrap();
        assert_eq!(
            usize::from(args.text_range().start())..usize::from(args.text_range().end()),
            open.start..close.end
        );
        let close_token = root
            .descendants_with_tokens()
            .filter_map(|element| element.into_token())
            .find(|token| token.kind() == SyntaxKind::RParen)
            .unwrap();
        assert_eq!(
            usize::from(close_token.text_range().start())
                ..usize::from(close_token.text_range().end()),
            close
        );
        assert_eq!(close_token.parent().unwrap().kind(), args_kind);
        let whitespace = root
            .descendants_with_tokens()
            .filter_map(|element| element.into_token())
            .find(|token| token.kind() == SyntaxKind::Whitespace)
            .unwrap();
        assert_eq!(whitespace.parent().unwrap().kind(), args_kind);
    }
}

#[test]
fn gate3_borrowed_close_rejects_an_adjacent_close_without_emitting_it() {
    let source = "\\ref(x.)tail";
    let open = 4..5;
    let mut remainder = &source[open.end..];
    let mut recovery = PilotRecoverState::default();
    recovery.line.column = open.end;
    recovery.line.at_line_start = false;
    let mut output = PilotOutput::new(source);
    output.start_node(SyntaxKind::Root);
    output.token_range(SyntaxKind::Unknown, 0..open.start);
    let rejected = present_borrowed_args(
        In::new(&mut remainder, &mut recovery, &mut output),
        PilotContext { root: source },
        BorrowedArgsOwner::InlineReference,
        open,
        PilotFrame::default(),
    )
    .expect_err("an empty-leading-trivia close is not the Gate 3 borrowed close");
    output.finish_node();

    assert_eq!(remainder, "tail");
    assert!(matches!(
        rejected.end.item.payload,
        Payload::Boundary(Boundary::Close(Delimiter::Parenthesis))
    ));
    assert_eq!(rejected.end.item.leading_trivia.text, "");
    assert_eq!(rejected.end.item.extent, 7..8);
    assert_eq!(rejected.end.item.logical_position.line, 0);
    assert_eq!(rejected.end.item.logical_position.column, 7);
    assert!(matches!(
        rejected.expression.items(),
        [
            OperatorChainItem::Primary(PrimaryExpression::Identifier(name)),
            OperatorChainItem::FixedPostfix(FixedPostfixTail::Field(field)),
        ] if name.text() == "x" && field.name() == &Recovered::Incomplete
    ));
    let root = SyntaxNode::new_root(output.finish_prefix());
    assert_eq!(root.to_string(), "\\ref(x.");
    assert!(
        root.descendants_with_tokens()
            .all(|element| element.kind() != SyntaxKind::RParen)
    );
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
    let source = "p  +x";
    let context = PilotContext { root: source };
    let frame = PilotFrame {
        layout_baseline: 3,
        allow_same_level_newline: true,
        delimiter: Some(Delimiter::Brace),
        ..PilotFrame::default()
    };
    let mut remainder = &source[1..];
    let mut recovery = PilotRecoverState::default();
    recovery.line.column = 1;
    recovery.line.at_line_start = false;
    let item = tail_item(In::new(&mut remainder, &mut recovery, ()), context, frame).unwrap();
    recovery.line.line_start = 7;
    recovery.record_expectation(expectation(4..4));
    let _ = recovery.allocate_diagnostic_id();
    recovery.record_provisional_recovery(ProvisionalRecovery {
        site: RecoverySiteKey {
            role: GrammarRole::Expression(ExpressionRole::Nud),
            range: 4..4,
        },
        kind: RecoveryKind::Missing,
    });
    recovery.record_persistent_recovery(PersistentRecovery {
        site: RecoverySiteKey {
            role: GrammarRole::Expression(ExpressionRole::MlArgument),
            range: 1..4,
        },
        kind: RecoveryKind::Error,
    });
    recovery.is_cut = true;
    let expected_remainder = remainder;
    let expected_line = recovery.line;
    let expected_next_item_ordinal = recovery.next_item_ordinal;
    let expected_scans = recovery.scanned_items().to_vec();
    let expected_expectations = recovery.expectations().to_vec();
    let expected_next_diagnostic_id = recovery.next_diagnostic_id();
    let expected_provisional = recovery.provisional_recoveries().to_vec();
    let expected_persistent = recovery.persistent_recoveries().to_vec();
    let expected_is_cut = recovery.is_cut;
    let expected_item = item.clone();
    let expected_frame = frame;
    let mut output = PilotOutput::new(source);
    output.start_node(SyntaxKind::Root);
    output.token_range(SyntaxKind::Unknown, 0..1);
    let committed_expectation = SyntaxExpectation {
        role: GrammarRole::Expression(ExpressionRole::Nud),
        expected: ExpectedSyntax::Expression,
        range: 1..1,
        sources: ExpectationSources::COMMITTED_RECOVERY_RULE,
    };
    output.publish_recovery(
        DiagnosticId(41),
        RecoveryDraft {
            site: RecoverySiteKey {
                role: committed_expectation.role,
                range: committed_expectation.range.clone(),
            },
            kind: RecoveryKind::Missing,
            unexpected: Arc::from([]),
            expectations: Arc::from([committed_expectation]),
            primary_expectation: 0,
            continuation: CanonicalRecoveryContinuation::StopAtBoundary,
        },
        1..1,
        RecoveryChainItem::None,
    );
    output.start_node(SyntaxKind::OperatorChain);
    output.begin_chain(item.extent.start);
    let expected_committed_recoveries = output.recoveries().to_vec();
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
    assert_eq!(returned.logical_position.column, 3);
    assert_eq!(remainder, expected_remainder);
    assert_eq!(remainder.as_ptr(), expected_remainder.as_ptr());
    assert_eq!(recovery.line, expected_line);
    assert_eq!(recovery.next_item_ordinal, expected_next_item_ordinal);
    assert_eq!(recovery.expectations(), expected_expectations);
    assert_eq!(recovery.next_diagnostic_id(), expected_next_diagnostic_id);
    assert_eq!(recovery.provisional_recoveries(), expected_provisional);
    assert_eq!(recovery.persistent_recoveries(), expected_persistent);
    assert_eq!(recovery.is_cut, expected_is_cut);
    assert_eq!(recovery.scanned_items(), expected_scans);
    assert_eq!(frame, expected_frame);
    assert!(output.root_chain().is_none());
    assert_eq!(output.recoveries(), expected_committed_recoveries);
    let unchanged_chain = output.finish_chain();
    assert!(unchanged_chain.items().is_empty());
    output.finish_node();
    output.finish_node();
    assert_eq!(output.finish_prefix().to_string(), "p");
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
