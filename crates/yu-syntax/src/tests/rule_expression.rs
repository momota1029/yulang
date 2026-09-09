use crate::tests::support::*;
use crate::{
    ambient_claim::AmbientClaimView,
    handoff::MlMode,
    lexical::yumark::{FenceOpener, FencePrefixPolicy},
    recovery_record::{GrammarRole, LiteralRole, RecoveryKind},
    statement::StatementLineHandoff,
};

fn parse<'s>(
    source: &'s str,
    pattern: bool,
    fence: Option<&FenceBoundary>,
) -> (
    GreenNode,
    Vec<CommittedRecoveryRecord>,
    NormalizedExit,
    &'s str,
) {
    let operators = OperatorTable::empty();
    parse_with(source, pattern, fence, &operators)
}

fn parse_with<'s>(
    source: &'s str,
    pattern: bool,
    fence: Option<&FenceBoundary>,
    operators: &OperatorTable,
) -> (
    GreenNode,
    Vec<CommittedRecoveryRecord>,
    NormalizedExit,
    &'s str,
) {
    let mut recover = Recover::new_for_test(operators);
    let mut input = source;
    let mut output = GreenNodeBuilder::new();
    output.start_node(SyntaxKind::Root.into());
    let ambient = Some(AmbientClaimView::root_statement(0)).into();
    let exit = if pattern {
        pattern_normalized(
            crate::cursor::SyntaxIn::new(&mut input, &mut recover, &mut output),
            0,
            LineEntry::InLine,
            fence,
            0,
            ambient,
        )
    } else {
        expr_normalized(
            crate::cursor::SyntaxIn::new(&mut input, &mut recover, &mut output),
            None,
            0,
            0,
            MlMode::All,
            StatementLineHandoff::OrdinaryLayout,
            0,
            LineEntry::InLine,
            fence,
            ambient,
            None,
        )
        .expect("ordinary identifier or RuleExpression NUD")
    };
    output.finish_node();
    let (green, records) = (output.finish(), recover.finish_recoveries_for_test());
    (green, records, exit, input)
}

fn count(green: &GreenNode, kind: SyntaxKind) -> usize {
    SyntaxNode::new_root(green.clone())
        .descendants()
        .filter(|node| node.kind() == kind)
        .count()
}

#[test]
fn contextual_rule_expression_and_pattern_accept_introducer_trivia() {
    for pattern in [false, true] {
        for source in [
            "rule{}",
            "rule {a}",
            "rule /* c */ {a}",
            "rule\n{a}",
            "rule\r\n{a}",
            "rule // c\n{a}",
            "rule /* a\r\nb */ {α}",
            "rule {a*? | b+?\nc = d}",
            "rule {f(x)[y]}",
        ] {
            let (green, records, _, rest) = parse(source, pattern, None);
            assert_eq!(green.to_string(), source, "{source:?}, pattern={pattern}");
            assert_eq!(rest, "");
            assert!(records.is_empty(), "{source:?}: {records:?}");
            assert_eq!(count(&green, SyntaxKind::RuleExpression), 1);
            assert_eq!(count(&green, SyntaxKind::RuleBody), 1);
            let root = SyntaxNode::new_root(green);
            assert_eq!(
                root.descendants_with_tokens()
                    .filter_map(|it| it.into_token())
                    .filter(|it| it.kind() == SyntaxKind::RuleKw)
                    .count(),
                1
            );
        }
    }
}

#[test]
fn contextual_rule_fallback_preserves_ordinary_word_and_successor() {
    for pattern in [false, true] {
        for source in [
            "rule",
            "rulex",
            "rule?",
            "rule!",
            "rule x",
            "rule,rest",
            "rule\nnext",
        ] {
            let (green, records, _, _) = parse(source, pattern, None);
            assert_eq!(count(&green, SyntaxKind::RuleExpression), 0, "{source:?}");
            assert!(records.is_empty(), "{source:?}: {records:?}");
            assert!(green.to_string().starts_with("rule"));
        }
        let (green, records, exit, rest) = parse("rule /* gap */ ,rest", pattern, None);
        assert_eq!(green.to_string(), "rule");
        assert!(records.is_empty());
        assert_eq!(rest, "rest");
        let NormalizedExit::Complete(Err(Either::Left(item)), _) = exit else {
            panic!("comma stays pending")
        };
        assert_eq!(token_kind(&item), Some(TokenKind::Comma));
        assert_eq!(item.extent(16).recovery_range(), 4..16);
    }
}

#[test]
fn contextual_rule_returns_to_its_own_expression_or_pattern_tail() {
    for (pattern, source, tail) in [
        (false, "rule {a}.field", SyntaxKind::FieldTail),
        (false, "rule {a}(x)", SyntaxKind::CallTail),
        (false, "rule {a} = x", SyntaxKind::AssignmentTail),
        (false, "rule {a} as int", SyntaxKind::TypeAnnotationTail),
        (false, "rule {a} x", SyntaxKind::MlArgument),
        (true, "rule {a}: int", SyntaxKind::PatternTypeAnnotation),
    ] {
        let (green, records, _, rest) = parse(source, pattern, None);
        assert_eq!(green.to_string(), source);
        assert!(records.is_empty(), "{records:?}");
        assert_eq!(rest, "");
        assert_eq!(count(&green, tail), 1);
        assert_eq!(count(&green, SyntaxKind::RuleExpression), 1);
    }
}

#[test]
fn contextual_rule_keeps_registered_word_operator_classification() {
    for (source, fixities, kind) in [
        (
            "rule",
            OperatorFixities::new().with_nullfix(),
            SyntaxKind::NullfixOperatorUse,
        ),
        (
            "rule x",
            OperatorFixities::new().with_prefix(BindingPower::scalar(70)),
            SyntaxKind::PrefixOperatorUse,
        ),
        (
            "rule {x}",
            OperatorFixities::new().with_prefix(BindingPower::scalar(70)),
            SyntaxKind::PrefixOperatorUse,
        ),
        (
            "a rule {x}",
            OperatorFixities::new().with_infix(BindingPower::scalar(40), BindingPower::scalar(41)),
            SyntaxKind::InfixOperatorUse,
        ),
    ] {
        let operators =
            OperatorTable::from_declarations([OperatorDeclaration::new("rule", fixities)]).unwrap();
        let (green, records, _, rest) = parse_with(source, false, None, &operators);
        assert!(records.is_empty(), "{source:?}: {records:?}");
        assert_eq!(rest, "");
        assert_eq!(green.to_string(), source);
        assert_eq!(count(&green, kind), 1, "{source:?}");
        assert_eq!(count(&green, SyntaxKind::RuleExpression), 0);
    }
}

#[test]
fn contextual_rule_reserves_its_brace_in_an_if_condition() {
    let source = "if rule {a}: body";
    let (green, records, _, rest) = parse(source, false, None);
    assert_eq!(green.to_string(), source);
    assert!(records.is_empty(), "{records:?}");
    assert_eq!(rest, "");
    assert_eq!(count(&green, SyntaxKind::RuleExpression), 1);
    let root = SyntaxNode::new_root(green);
    let arm = root
        .descendants()
        .find(|node| node.kind() == SyntaxKind::IfArm)
        .expect("if arm");
    let condition = arm
        .children()
        .find(|node| node.kind() == SyntaxKind::Condition)
        .expect("condition wrapper");
    assert_eq!(condition.text().to_string(), "rule {a}");
    assert!(
        condition
            .descendants()
            .any(|node| node.kind() == SyntaxKind::RuleExpression)
    );
    let body = arm
        .children()
        .find(|node| node.kind() == SyntaxKind::OperatorChain)
        .expect("inline body chain");
    assert_eq!(body.text().to_string(), "body");
    assert!(arm.children_with_tokens().any(|element| {
        element
            .into_token()
            .is_some_and(|token| token.kind() == SyntaxKind::Colon)
    }));
}

#[test]
fn contextual_rule_missing_body_close_preserves_eof_and_outer_close() {
    for pattern in [false, true] {
        for (source, emitted, at) in [("rule {a", "rule {a", 7), ("rule {a ]rest", "rule {a", 7)] {
            let (green, records, exit, rest) = parse(source, pattern, None);
            assert_eq!(green.to_string(), emitted);
            assert_eq!(records.len(), 1);
            assert_eq!(
                records[0].site.role,
                GrammarRole::Literal(LiteralRole::RuleBodyCloseBrace)
            );
            assert_eq!(records[0].site.range, at..at);
            assert_eq!(records[0].kind, RecoveryKind::Missing);
            if source.ends_with("rest") {
                assert_eq!(rest, "rest");
                let NormalizedExit::Complete(Err(Either::Left(item)), _) = exit else {
                    panic!("outer close stays pending")
                };
                assert_eq!(token_kind(&item), Some(TokenKind::RBracket));
                assert_eq!(item.extent(9).recovery_range(), 7..9);
            }
        }
    }
}

#[test]
fn contextual_rule_introducer_and_body_preserve_fence_boundaries() {
    let fence = FenceBoundary {
        opener: FenceOpener {
            line: 0,
            marker: 0..3,
            marker_width: 3,
        },
        prefix_policy: FencePrefixPolicy::ActivePrefixQuote { depth: 2, base: 0 },
        close_column: 0,
    };
    for pattern in [false, true] {
        for (source, emitted, rules, missing) in [
            ("rule\n> stop\n", "rule", 0, 0),
            ("rule {a\n> stop\n", "rule {a", 1, 1),
        ] {
            let (green, records, exit, rest) = parse(source, pattern, Some(&fence));
            assert_eq!(green.to_string(), emitted);
            assert_eq!(records.len(), missing);
            assert_eq!(count(&green, SyntaxKind::RuleExpression), rules);
            assert_eq!(rest, "> stop\n");
            let NormalizedExit::Complete(Err(Either::Left(item)), LineEntry::PhysicalStart) = exit
            else {
                panic!("same fence boundary")
            };
            assert!(item.payload_view().is_boundary());
            assert_eq!(rest.as_ptr(), source[source.len() - rest.len()..].as_ptr());
        }
        let source = "rule\r\n> > {α}\n> stop\n";
        let (green, records, _, rest) = parse(source, pattern, Some(&fence));
        assert_eq!(green.to_string(), "rule\r\n> > {α}");
        assert!(records.is_empty());
        assert_eq!(count(&green, SyntaxKind::RuleExpression), 1);
        assert_eq!(rest, "> stop\n");
    }
}
