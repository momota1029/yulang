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
fn type_annotation_required_type_schema_preserves_native_error_and_retry_leading() {
    use SyntaxKind::*;
    let assert_elements =
        |parent: &SyntaxNode, expected: &[(SyntaxKind, bool, std::ops::Range<u32>, &str)]| {
            let children = parent.children_with_tokens().collect::<Vec<_>>();
            assert_eq!(children.len(), expected.len());
            for (child, (kind, node, range, text)) in children.iter().zip(expected) {
                assert_eq!(child.parent(), Some(parent.clone()));
                assert_eq!(child.kind(), *kind);
                assert_eq!(child.as_node().is_some(), *node);
                assert_eq!(
                    child.text_range(),
                    rowan::TextRange::new(range.start.into(), range.end.into())
                );
                assert_eq!(child.to_string(), *text);
            }
        };
    for (source, owned, suffix, type_children) in [
        (
            "x as Int",
            "x as Int",
            vec![(TypeExpression, true, 4..8, " Int")],
            vec![
                (Whitespace, false, 4..5, " "),
                (Identifier, false, 5..8, "Int"),
            ],
        ),
        (
            "x as @",
            "x as @",
            vec![(Error, false, 4..5, " "), (Error, false, 5..6, "@")],
            vec![],
        ),
        (
            "x as @ Int",
            "x as @ Int",
            vec![
                (Error, false, 4..5, " "),
                (Error, false, 5..6, "@"),
                (TypeExpression, true, 6..10, " Int"),
            ],
            vec![
                (Whitespace, false, 6..7, " "),
                (Identifier, false, 7..10, "Int"),
            ],
        ),
        (
            "x as @  ~   型",
            "x as @  ~   型",
            vec![
                (Error, false, 4..5, " "),
                (Error, false, 5..6, "@"),
                (Error, false, 6..8, "  "),
                (Error, false, 8..9, "~"),
                (TypeExpression, true, 9..15, "   型"),
            ],
            vec![
                (Whitespace, false, 9..12, "   "),
                (Identifier, false, 12..15, "型"),
            ],
        ),
        (
            "x as @ ]",
            "x as @",
            vec![(Error, false, 4..5, " "), (Error, false, 5..6, "@")],
            vec![],
        ),
    ] {
        let (green, records, exit, rest) = parse(source, None, MlMode::All, 0, None);
        assert_eq!(green.to_string(), owned);
        assert_eq!(rest, "");
        let root = SyntaxNode::new_root(green.clone());
        assert_eq!(root.kind(), Root);
        assert!(root.parent().is_none());
        let chain = root.first_child().expect("OperatorChain");
        let end = owned.len() as u32;
        assert_elements(&root, &[(OperatorChain, true, 0..end, owned)]);
        assert_elements(
            &chain,
            &[
                (IdentifierExpression, true, 0..1, "x"),
                (Whitespace, false, 1..2, " "),
                (TypeAnnotationTail, true, 2..end, &owned[2..]),
            ],
        );
        let tail = chain.last_child().expect("TypeAnnotationTail");
        assert_eq!(tail.kind(), TypeAnnotationTail);
        let mut expected = vec![(AsKw, false, 2..4, "as")];
        expected.extend(suffix);
        assert_elements(&tail, &expected);
        assert!(
            !root
                .descendants_with_tokens()
                .any(|child| matches!(child.kind(), Missing | Invalid))
        );

        // Direct TypeAnnotationTail children after AsKw are the required-Type
        // phase. Its Error group is Type Primary, not annotation Missing.
        // A following TypeExpression ends the group and owns retry leading.
        let children = tail.children_with_tokens().collect::<Vec<_>>();
        assert_eq!(children[0].kind(), AsKw);
        let errors = children[1..]
            .iter()
            .take_while(|child| child.kind() == Error)
            .collect::<Vec<_>>();
        assert_eq!(
            root.descendants_with_tokens()
                .filter(|child| child.kind() == Error)
                .count(),
            errors.len()
        );
        if let Some(first) = errors.first() {
            assert_eq!(first.text_range().start(), 4.into());
            let group_end = if errors.len() == 4 { 9 } else { 6 };
            assert_eq!(errors.last().unwrap().text_range().end(), group_end.into());
            for pair in errors.windows(2) {
                assert_eq!(pair[0].text_range().end(), pair[1].text_range().start());
            }
            if let Some(ty) = tail.first_child() {
                assert_eq!(ty.kind(), TypeExpression);
                assert_eq!(ty.text_range().start(), group_end.into());
            }
        }
        if type_children.is_empty() {
            assert_eq!(tail.children().count(), 0);
        } else {
            assert_eq!(tail.children().count(), 1);
            assert_elements(&tail.first_child().unwrap(), &type_children);
        }

        let assert_handoff = |exit| {
            let mut item = match exit {
                NormalizedExit::Complete(Err(Either::Left(item)), entry) => {
                    assert_eq!(entry, LineEntry::InLine);
                    item
                }
                NormalizedExit::Complete(Err(Either::Right(end)), entry) => {
                    assert_eq!(entry, LineEntry::InLine);
                    end.item
                }
                _ => panic!("pending EOF or close"),
            };
            if source == "x as @ ]" {
                assert_eq!(token_kind(&item), Some(TokenKind::RBracket));
                assert_eq!(item.payload_view().spelling(), Some("]"));
                assert_eq!(item.extent(8).recovery_range(), 6..8);
                assert_eq!(emit_pending_leading_text(&mut item), " ");
                assert_eq!(item.extent(8).recovery_range(), 7..8);
            } else {
                assert!(item.payload_view().is_eof());
                assert_eq!(emit_pending_leading_text(&mut item), "");
            }
        };
        assert_handoff(exit);
        // Record identity is only a compatibility oracle after the CST proof.
        assert_eq!(records.len(), usize::from(!errors.is_empty()));
        if let Some(record) = records.first() {
            assert_eq!(record.kind, RecoveryKind::Error);
            assert_eq!(record.site.role, GrammarRole::Type(TypeRole::Primary));
            assert_eq!(record.site.range, 4..if errors.len() == 4 { 9 } else { 6 });
        }
        let (again, frozen, again_exit, again_rest) =
            parse(source, None, MlMode::All, 0, Some(&records));
        assert_eq!(again, green);
        assert_eq!(frozen, records);
        assert_eq!(again_rest, rest);
        assert_handoff(again_exit);
    }
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
fn annotation_required_type_missing_has_a_direct_structural_slot() {
    use crate::recovery_record::ExpectedSyntax;

    for source in ["x as", "x as ]"] {
        let (green, _records, exit, rest) = parse(source, None, MlMode::All, 0, None);
        assert_eq!(green.to_string(), "x as");
        assert_eq!(rest, "");
        let root = SyntaxNode::new_root(green);
        let chain = root.first_child().expect("outer OperatorChain");
        assert_eq!(chain.kind(), SyntaxKind::OperatorChain);
        let tail = chain.children().last().expect("TypeAnnotationTail");
        assert_eq!(tail.kind(), SyntaxKind::TypeAnnotationTail);
        assert_eq!(tail.parent(), Some(chain));
        let children = tail.children_with_tokens().collect::<Vec<_>>();
        assert_eq!(children.len(), 2);
        let keyword = children[0].as_token().expect("exact as introducer");
        assert_eq!(keyword.kind(), SyntaxKind::AsKw);
        assert_eq!(keyword.text(), "as");
        assert_eq!(usize::from(keyword.text_range().start()), 2);
        assert_eq!(usize::from(keyword.text_range().end()), 4);
        assert_eq!(keyword.parent(), Some(tail.clone()));
        let type_expr = children[1].as_node().expect("required TypeExpression");
        assert_eq!(type_expr.kind(), SyntaxKind::TypeExpression);
        assert_eq!(usize::from(type_expr.text_range().start()), 4);
        assert_eq!(usize::from(type_expr.text_range().end()), 4);
        assert_eq!(type_expr.parent(), Some(tail.clone()));
        let type_children = type_expr.children_with_tokens().collect::<Vec<_>>();
        assert_eq!(type_children.len(), 1);
        let missing = type_children[0].as_node().expect("required Type Missing");
        assert_eq!(missing.kind(), SyntaxKind::Missing);
        assert_eq!(usize::from(missing.text_range().start()), 4);
        assert_eq!(usize::from(missing.text_range().end()), 4);
        assert_eq!(missing.parent().as_ref(), Some(type_expr));
        assert_eq!(missing.children_with_tokens().count(), 0);
        assert_eq!(missing.to_string(), "");

        // The enclosing annotation slot selects the initial Type expectation;
        // a TypeExpression parent alone does not identify that slot.
        let selected = match (
            tail.kind(),
            children[0].kind(),
            type_expr.kind(),
            missing.kind(),
        ) {
            (
                SyntaxKind::TypeAnnotationTail,
                SyntaxKind::AsKw,
                SyntaxKind::TypeExpression,
                SyntaxKind::Missing,
            ) => (
                GrammarRole::Expression(ExpressionRole::TypeAnnotation),
                ExpectedSyntax::TypeExpression,
                0,
            ),
            _ => panic!("unrecognized required annotation Type slot"),
        };
        assert_eq!(
            selected,
            (
                GrammarRole::Expression(ExpressionRole::TypeAnnotation),
                ExpectedSyntax::TypeExpression,
                0,
            )
        );

        if source == "x as ]" {
            let NormalizedExit::Complete(Err(Either::Left(mut item)), _) = exit else {
                panic!("protected close remains pending")
            };
            assert_eq!(token_kind(&item), Some(TokenKind::RBracket));
            let extent = item.extent(source.len());
            assert_eq!(extent.leading(), 4..5);
            assert_eq!(extent.payload(), 5..6);
            assert_eq!(emit_pending_leading_text(&mut item), " ");
        }
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
