use crate::tests::support::*;
use crate::{
    ambient_claim::AmbientClaimView,
    handoff::MlMode,
    recovery_record::{AssignmentRole, ExpressionRole, GrammarRole, RecoveryKind, TypeRole},
    statement::StatementLineHandoff,
};

fn operators() -> OperatorTable {
    OperatorTable::from_declarations([
        OperatorDeclaration::new(
            "-",
            OperatorFixities::new().with_prefix(BindingPower::scalar(70)),
        ),
        OperatorDeclaration::new(
            "+",
            OperatorFixities::new()
                .with_prefix(BindingPower::scalar(70))
                .with_infix(BindingPower::scalar(50), BindingPower::scalar(51)),
        ),
        OperatorDeclaration::new(
            "==",
            OperatorFixities::new().with_infix(BindingPower::scalar(30), BindingPower::scalar(31)),
        ),
    ])
    .unwrap()
}

fn parse<'s>(
    source: &'s str,
    threshold: Option<&BindingPower>,
    mode: MlMode,
    stops: Stops,
    frozen: Option<&[CommittedRecoveryRecord]>,
) -> (
    GreenNode,
    Vec<CommittedRecoveryRecord>,
    NormalizedExit,
    &'s str,
) {
    parse_at(source, threshold, mode, stops, frozen, 0, None)
}

#[allow(clippy::too_many_arguments)]
fn parse_at<'s>(
    source: &'s str,
    threshold: Option<&BindingPower>,
    mode: MlMode,
    stops: Stops,
    frozen: Option<&[CommittedRecoveryRecord]>,
    origin: usize,
    fence: Option<&FenceBoundary>,
) -> (
    GreenNode,
    Vec<CommittedRecoveryRecord>,
    NormalizedExit,
    &'s str,
) {
    let operators = operators();
    let mut input = source;
    let mut recover = Recover::new_for_test(&operators);
    let mut output = frozen
        .map(|records| {
            recover = Recover::reconcile_for_test(recover.operators(), records);
            GreenNodeBuilder::new()
        })
        .unwrap_or_else(GreenNodeBuilder::new);
    output.start_node(SyntaxKind::Root.into());
    let exit = expr_normalized(
        crate::cursor::SyntaxIn::new(&mut input, &mut recover, &mut output),
        threshold,
        0,
        stops,
        mode,
        StatementLineHandoff::OrdinaryLayout,
        origin,
        LineEntry::InLine,
        fence,
        Some(AmbientClaimView::root_statement(0)).into(),
        None,
    )
    .unwrap();
    output.finish_node();
    let (green, records) = (output.finish(), recover.finish_recoveries_for_test());
    (green, records, exit, input)
}

#[test]
fn assignment_one_character_fallback_preserves_dynamic_led_priority_and_prefix_rhs() {
    for source in ["x=-y", "x=+y", "x = y", "x =\n  y"] {
        let (green, records, _, rest) = parse(source, None, MlMode::All, 0, None);
        assert_eq!(green.to_string(), source);
        assert!(records.is_empty(), "{source}: {records:?}");
        assert_eq!(rest, "");
        let root = SyntaxNode::new_root(green);
        assert_eq!(
            root.descendants()
                .filter(|node| node.kind() == SyntaxKind::AssignmentTail)
                .count(),
            1
        );
    }
    let (green, records, _, _) = parse("x==y", None, MlMode::All, 0, None);
    assert!(records.is_empty());
    assert_eq!(green.to_string(), "x==y");
    let root = SyntaxNode::new_root(green);
    assert!(
        !root
            .descendants()
            .any(|node| node.kind() == SyntaxKind::AssignmentTail)
    );
    assert!(
        root.descendants()
            .any(|node| node.kind() == SyntaxKind::InfixOperatorUse)
    );
}

#[test]
fn assignment_tail_keeps_rhs_and_recovery_in_the_direct_rowan_shape() {
    fn range(node: &SyntaxNode) -> std::ops::Range<usize> {
        usize::from(node.text_range().start())..usize::from(node.text_range().end())
    }

    let (green, records, _, rest) = parse("x = y", None, MlMode::All, 0, None);
    assert!(records.is_empty());
    assert_eq!(rest, "");
    let root = SyntaxNode::new_root(green);
    let chain = root.first_child().expect("outer OperatorChain");
    assert_eq!(chain.kind(), SyntaxKind::OperatorChain);
    let children = chain.children_with_tokens().collect::<Vec<_>>();
    assert_eq!(children.len(), 3);
    assert_eq!(
        children[0].as_node().map(SyntaxNode::kind),
        Some(SyntaxKind::IdentifierExpression)
    );
    assert_eq!(
        children[1].as_token().map(|token| token.kind()),
        Some(SyntaxKind::Whitespace)
    );
    let identifier = children[0].as_node().expect("IdentifierExpression");
    assert_eq!(identifier.parent(), Some(chain.clone()));
    let tail = children[2].as_node().expect("AssignmentTail");
    assert_eq!(tail.kind(), SyntaxKind::AssignmentTail);
    assert_eq!(range(tail), 2..5);
    assert_eq!(tail.parent(), Some(chain.clone()));
    let rhs = tail.children().last().expect("inline RHS OperatorChain");
    assert_eq!(rhs.kind(), SyntaxKind::OperatorChain);
    assert_eq!(range(&rhs), 4..5);
    assert_eq!(rhs.parent(), Some(tail.clone()));
    assert_eq!(
        rhs.first_child().map(|node| node.kind()),
        Some(SyntaxKind::IdentifierExpression)
    );
    let tail_children = tail.children_with_tokens().collect::<Vec<_>>();
    assert_eq!(tail_children.len(), 3);
    let equals = tail_children[0].as_token().expect("Equals token");
    assert_eq!(equals.kind(), SyntaxKind::Equals);
    assert_eq!(equals.text(), "=");
    assert_eq!(equals.parent(), Some(tail.clone()));
    let leading = tail_children[1].as_token().expect("RHS leading whitespace");
    assert_eq!(leading.kind(), SyntaxKind::Whitespace);
    assert_eq!(leading.text(), " ");
    assert_eq!(leading.parent(), Some(tail.clone()));
    assert_eq!(tail_children[2].as_node(), Some(&rhs));

    let (green, _records, exit, rest) = parse("x = ]", None, MlMode::All, 0, None);
    assert_eq!(rest, "");
    let NormalizedExit::Complete(Err(Either::Left(item)), _) = exit else {
        panic!("protected close remains unread");
    };
    assert_eq!(token_kind(&item), Some(TokenKind::RBracket));
    assert_eq!(item.extent(5).recovery_range(), 3..5);
    let root = SyntaxNode::new_root(green);
    let tail = root
        .descendants()
        .find(|node| node.kind() == SyntaxKind::AssignmentTail)
        .expect("AssignmentTail");
    let missing = tail.children().last().expect("RHS Missing");
    assert_eq!(missing.kind(), SyntaxKind::Missing);
    assert_eq!(range(&missing), 3..3);
    assert_eq!(missing.parent(), Some(tail));

    let (green, _records, exit, rest) = parse("x = @ ]", None, MlMode::All, 0, None);
    assert_eq!(rest, "");
    let NormalizedExit::Complete(Err(Either::Left(item)), _) = exit else {
        panic!("protected close remains unread after Error");
    };
    assert_eq!(token_kind(&item), Some(TokenKind::RBracket));
    assert_eq!(item.extent(7).recovery_range(), 5..7);
    let root = SyntaxNode::new_root(green);
    let tail = root
        .descendants()
        .find(|node| node.kind() == SyntaxKind::AssignmentTail)
        .expect("AssignmentTail");
    let children = tail.children_with_tokens().collect::<Vec<_>>();
    assert_eq!(children.len(), 3);
    let equals = children[0].as_token().expect("Equals token");
    assert_eq!(equals.kind(), SyntaxKind::Equals);
    assert_eq!(equals.text(), "=");
    assert_eq!(equals.parent(), Some(tail.clone()));
    let leading = children[1].as_token().expect("Error leading whitespace");
    assert_eq!(leading.kind(), SyntaxKind::Whitespace);
    assert_eq!(leading.text(), " ");
    assert_eq!(leading.parent(), Some(tail.clone()));
    let error = children[2].as_token().expect("raw Error token");
    assert_eq!(error.kind(), SyntaxKind::Error);
    assert_eq!(error.text(), "@");
    assert_eq!(
        usize::from(error.text_range().start())..usize::from(error.text_range().end()),
        4..5
    );
    assert_eq!(error.parent(), Some(tail));

    let (green, _records, _, rest) = parse("x = @ y", None, MlMode::All, 0, None);
    assert_eq!(rest, "");
    let root = SyntaxNode::new_root(green);
    let tail = root
        .descendants()
        .find(|node| node.kind() == SyntaxKind::AssignmentTail)
        .expect("AssignmentTail");
    let children = tail.children_with_tokens().collect::<Vec<_>>();
    assert_eq!(children.len(), 4);
    let equals = children[0].as_token().expect("Equals token");
    assert_eq!(equals.kind(), SyntaxKind::Equals);
    assert_eq!(equals.text(), "=");
    assert_eq!(equals.parent(), Some(tail.clone()));
    let leading = children[1].as_token().expect("Error leading whitespace");
    assert_eq!(leading.kind(), SyntaxKind::Whitespace);
    assert_eq!(leading.text(), " ");
    assert_eq!(leading.parent(), Some(tail.clone()));
    assert_eq!(
        children[2].as_token().map(|token| token.kind()),
        Some(SyntaxKind::Error)
    );
    let rhs = children[3].as_node().expect("retried RHS OperatorChain");
    assert_eq!(rhs.kind(), SyntaxKind::OperatorChain);
    assert_eq!(range(&rhs), 5..7);
    assert_eq!(rhs.parent(), Some(tail));
    let retry_leading = rhs.first_token().expect("retry leading whitespace");
    assert_eq!(retry_leading.kind(), SyntaxKind::Whitespace);
    assert_eq!(retry_leading.text(), " ");
    assert_eq!(
        usize::from(retry_leading.text_range().start())
            ..usize::from(retry_leading.text_range().end()),
        5..6
    );
    let retry_owner = retry_leading.parent().expect("retry leading owner");
    assert_eq!(retry_owner.kind(), SyntaxKind::IdentifierExpression);
    assert_eq!(retry_owner.parent(), Some(rhs.clone()));

    let (green, _records, exit, rest) = parse("x = @  @ ]", None, MlMode::All, 0, None);
    assert_eq!(rest, "");
    let NormalizedExit::Complete(Err(Either::Left(item)), _) = exit else {
        panic!("protected close remains unread after a fragmented Error run");
    };
    assert_eq!(token_kind(&item), Some(TokenKind::RBracket));
    assert_eq!(item.extent(10).recovery_range(), 8..10);
    let root = SyntaxNode::new_root(green);
    let tail = root
        .descendants()
        .find(|node| node.kind() == SyntaxKind::AssignmentTail)
        .expect("AssignmentTail");
    let children = tail.children_with_tokens().collect::<Vec<_>>();
    assert_eq!(
        children
            .iter()
            .map(|element| element.kind())
            .collect::<Vec<_>>(),
        [
            SyntaxKind::Equals,
            SyntaxKind::Whitespace,
            SyntaxKind::Error,
            SyntaxKind::Error,
            SyntaxKind::Error,
        ]
    );
    let errors = children
        .into_iter()
        .filter_map(|element| element.into_token())
        .filter(|token| token.kind() == SyntaxKind::Error)
        .collect::<Vec<_>>();
    assert_eq!(errors.len(), 3);
    assert_eq!(
        errors.iter().map(|token| token.text()).collect::<Vec<_>>(),
        ["@", "  ", "@"]
    );
    let ranges = errors
        .iter()
        .map(|token| usize::from(token.text_range().start())..usize::from(token.text_range().end()))
        .collect::<Vec<_>>();
    assert_eq!(ranges, [4..5, 5..7, 7..8]);
    assert!(ranges.windows(2).all(|pair| pair[0].end == pair[1].start));
    assert_eq!(ranges[0].start..ranges[2].end, 4..8);
    assert_eq!(&"x = @  @ ]"[4..8], "@  @");
    assert_eq!(errors[1].parent(), Some(tail));

    let (green, _records, _, rest) = parse("x = y.", None, MlMode::All, 0, None);
    assert_eq!(rest, "");
    let root = SyntaxNode::new_root(green);
    let tail = root
        .descendants()
        .find(|node| node.kind() == SyntaxKind::AssignmentTail)
        .expect("AssignmentTail");
    let rhs = tail.children().last().expect("RHS OperatorChain");
    let field = rhs
        .children()
        .find(|node| node.kind() == SyntaxKind::FieldTail)
        .expect("nested FieldTail");
    assert_eq!(field.parent(), Some(rhs));
    let missing = field.children().last().expect("FieldTail Missing");
    assert_eq!(missing.kind(), SyntaxKind::Missing);
    assert_eq!(range(&missing), 6..6);
    assert_eq!(missing.parent(), Some(field));
}

#[test]
fn assignment_single_rhs_returns_separator_without_outer_continuation() {
    let (green, records, exit, rest) = parse("x = y, z", None, MlMode::All, 0, None);
    assert_eq!(green.to_string(), "x = y");
    assert!(records.is_empty());
    assert_eq!(rest, " z");
    let NormalizedExit::Complete(Err(Either::Left(item)), _) = exit else {
        panic!("pending comma")
    };
    assert_eq!(token_kind(&item), Some(TokenKind::Comma));
    let root = SyntaxNode::new_root(green);
    let outer = root.first_child().unwrap();
    assert_eq!(
        outer.children().map(|node| node.kind()).collect::<Vec<_>>(),
        [SyntaxKind::IdentifierExpression, SyntaxKind::AssignmentTail]
    );
}

#[test]
fn structural_tail_threshold_and_ml_rejection_emit_no_tail_or_recovery() {
    let bp = BindingPower::scalar(10);
    for (threshold, mode) in [(Some(&bp), MlMode::All), (None, MlMode::None)] {
        for source in ["x=y", "x as Int"] {
            let (green, records, _, _) = parse(source, threshold, mode, 0, None);
            assert!(records.is_empty());
            assert_eq!(green.to_string(), "x");
            let root = SyntaxNode::new_root(green);
            assert!(!root.descendants().any(|node| matches!(
                node.kind(),
                SyntaxKind::AssignmentTail | SyntaxKind::TypeAnnotationTail
            )));
        }
    }
}

#[test]
fn annotation_owns_full_type_and_propagates_type_stops() {
    for source in ["x as Int", "x as int as str", "x as int y", "x as (Int)"] {
        let (green, records, _, _) = parse(source, None, MlMode::All, 0, None);
        assert!(records.is_empty(), "{source}: {records:?}");
        assert_eq!(green.to_string(), source);
        assert!(
            SyntaxNode::new_root(green)
                .descendants()
                .any(|node| node.kind() == SyntaxKind::TypeAnnotationTail)
        );
    }
    for (source, token, rest) in [
        ("x as int + y", TokenKind::Unknown, " y"),
        ("x as int; y", TokenKind::Semicolon, " y"),
    ] {
        let (green, records, exit, remaining) = parse(source, None, MlMode::All, 0, None);
        assert_eq!(green.to_string(), "x as int");
        assert!(records.is_empty());
        assert_eq!(remaining, rest);
        let NormalizedExit::Complete(Err(Either::Left(item)), _) = exit else {
            panic!("pending Type stop")
        };
        assert_eq!(token_kind(&item), Some(token));
    }
}

#[test]
fn structural_tail_initial_missing_and_type_error_roles_survive_reconciliation() {
    for (source, role, kind, range) in [
        (
            "x =",
            GrammarRole::Assignment(AssignmentRole::Rhs),
            RecoveryKind::Missing,
            3..3,
        ),
        (
            "x = ]",
            GrammarRole::Assignment(AssignmentRole::Rhs),
            RecoveryKind::Missing,
            3..3,
        ),
        (
            "x = [",
            GrammarRole::Assignment(AssignmentRole::Rhs),
            RecoveryKind::Missing,
            3..3,
        ),
        (
            "x = ,",
            GrammarRole::Assignment(AssignmentRole::Rhs),
            RecoveryKind::Missing,
            3..3,
        ),
        (
            "x =\ny",
            GrammarRole::Assignment(AssignmentRole::Rhs),
            RecoveryKind::Missing,
            3..3,
        ),
        (
            "x = @ ]",
            GrammarRole::Assignment(AssignmentRole::Rhs),
            RecoveryKind::Error,
            4..5,
        ),
        (
            "x = @ y",
            GrammarRole::Assignment(AssignmentRole::Rhs),
            RecoveryKind::Error,
            4..5,
        ),
        (
            "x as",
            GrammarRole::Expression(ExpressionRole::TypeAnnotation),
            RecoveryKind::Missing,
            4..4,
        ),
        (
            "x as ]",
            GrammarRole::Expression(ExpressionRole::TypeAnnotation),
            RecoveryKind::Missing,
            4..4,
        ),
        (
            "x as @",
            GrammarRole::Type(TypeRole::Primary),
            RecoveryKind::Error,
            4..6,
        ),
    ] {
        let (green, records, _, _) = parse(source, None, MlMode::All, 0, None);
        assert_eq!(records.len(), 1, "{source}: {records:?}");
        assert_eq!(records[0].site.role, role, "{source}");
        assert_eq!(records[0].site.range, range, "{source}");
        assert_eq!(records[0].kind, kind, "{source}");
        let (frozen_green, frozen, _, _) = parse(source, None, MlMode::All, 0, Some(&records));
        assert_eq!(green, frozen_green);
        assert_eq!(records, frozen);
    }
}

#[test]
fn assignment_boundaries_before_and_after_error_preserve_whole_items() {
    use crate::lexical::stops::{STOP_COLON, STOP_COMMA, STOP_LINE_BREAK};
    for (suffix, stops, pending) in [
        (" , next", STOP_COMMA, TokenKind::Comma),
        (" : next", STOP_COLON, TokenKind::Colon),
        (" ] next", 0, TokenKind::RBracket),
        (" [ next", 0, TokenKind::LBracket),
        ("\nnext", STOP_LINE_BREAK, TokenKind::Identifier),
    ] {
        for (prefix, kind, emitted) in [
            ("x =", RecoveryKind::Missing, "x ="),
            ("x = @", RecoveryKind::Error, "x = @"),
        ] {
            let source = format!("{prefix}{suffix}");
            let (green, records, exit, rest) = parse(&source, None, MlMode::All, stops, None);
            assert_eq!(green.to_string(), emitted);
            assert_eq!(records.len(), 1);
            assert_eq!(records[0].kind, kind);
            let NormalizedExit::Complete(Err(Either::Left(item)), _) = exit else {
                panic!("protected Item")
            };
            assert_eq!(token_kind(&item), Some(pending));
            assert_eq!(
                item.extent(source.len() - rest.len())
                    .recovery_range()
                    .start,
                prefix.len()
            );
        }
    }
}

#[test]
fn structural_tail_utf8_crlf_fences_preserve_source_coordinates() {
    use crate::lexical::yumark::{FenceOpener, FencePrefixPolicy};
    let fence = FenceBoundary {
        opener: FenceOpener {
            line: 0,
            marker: 0..3,
            marker_width: 3,
        },
        prefix_policy: FencePrefixPolicy::ActivePrefixQuote { depth: 2, base: 0 },
        close_column: 0,
    };
    for (source, kind, range, emitted) in [
        (
            "x =\r\n> > ```\nouter",
            RecoveryKind::Missing,
            105..105,
            "x =",
        ),
        (
            "x = 💥\r\n> > ```\nouter",
            RecoveryKind::Error,
            104..108,
            "x = 💥",
        ),
        (
            "x as\r\n> > ```\nouter",
            RecoveryKind::Missing,
            106..106,
            "x as",
        ),
    ] {
        let (green, records, exit, _) =
            parse_at(source, None, MlMode::All, 0, None, 100, Some(&fence));
        assert_eq!(green.to_string(), emitted);
        assert_eq!(records.len(), 1);
        assert_eq!(records[0].kind, kind);
        assert_eq!(records[0].site.range, range);
        let NormalizedExit::Complete(Err(Either::Left(item)), _) = exit else {
            panic!("quoted fence")
        };
        assert!(item.payload_view().is_boundary());
    }
}

#[test]
fn assignment_newline_eof_is_protected_before_and_after_error() {
    use crate::recovery_record::{
        DiagnosticId, ExpectationSources, ExpectedSyntax, RecoverySiteKey, SyntaxExpectation,
        UnexpectedCategory, UnexpectedSyntax,
    };
    use std::sync::Arc;

    let role = GrammarRole::Assignment(AssignmentRole::Rhs);
    for (source, emitted, kind, range, pending_range) in [
        ("x =\n", "x =", RecoveryKind::Missing, 3..3, 3..4),
        ("x = @\n", "x = @", RecoveryKind::Error, 4..5, 5..6),
        ("x = ", "x = ", RecoveryKind::Missing, 4..4, 4..4),
    ] {
        let (green, records, exit, rest) = parse(source, None, MlMode::All, 0, None);
        assert_eq!(green.to_string(), emitted);
        assert_eq!(rest, "");
        assert_eq!(
            records,
            [CommittedRecoveryRecord {
                id: DiagnosticId(0),
                site: RecoverySiteKey {
                    role,
                    range: range.clone()
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
                    expected: ExpectedSyntax::Expression,
                    range,
                    sources: ExpectationSources::COMMITTED_RECOVERY_RULE,
                }]),
                primary_expectation: 0,
            }]
        );
        let NormalizedExit::Complete(Err(Either::Right(end)), _) = exit else {
            panic!("pending EOF Item")
        };
        assert_eq!(
            end.item.extent(source.len()).recovery_range(),
            pending_range
        );
        let mut pending = GreenNodeBuilder::new();
        let operators = OperatorTable::empty();
        let recover = Recover::new_for_test(&operators);
        pending.start_node(SyntaxKind::Root.into());
        let mut item = end.item;
        item.emit_eof_leading(&mut pending);
        pending.finish_node();
        let (pending, pending_records) = (pending.finish(), recover.finish_recoveries_for_test());
        assert_eq!(pending.to_string(), &source[emitted.len()..]);
        assert!(pending_records.is_empty());
    }
}
