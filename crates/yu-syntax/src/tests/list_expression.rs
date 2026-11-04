use crate::structural_diagnostic::StructuralKind;
use crate::tests::support::*;
use std::sync::Arc;

fn parse_file_clean(source: &str) -> SyntaxNode {
    let text: Arc<crate::SourceText> = Arc::from(source);
    let parsed = crate::parse_file(
        Arc::clone(&text),
        Arc::new(crate::scan_header(text)),
        Arc::new(crate::SyntaxEnvironment::empty()),
    );
    assert_eq!(parsed.green().to_string(), source, "{source:?}");
    assert!(
        parsed.syntax_diagnostics().unwrap().is_empty(),
        "{source:?}"
    );
    assert!(structural_facts(parsed.green()).is_empty(), "{source:?}");
    let root = SyntaxNode::new_root(parsed.green().clone());
    assert!(
        !root.descendants_with_tokens().any(|element| matches!(
            element.kind(),
            SyntaxKind::Error | SyntaxKind::Missing | SyntaxKind::Invalid
        )),
        "{source:?}"
    );
    root
}

fn direct_node_kinds(node: &SyntaxNode) -> Vec<SyntaxKind> {
    node.children().map(|child| child.kind()).collect()
}

#[test]
fn list_literals_accept_empty_items_spreads_nesting_and_expression_contexts() {
    for source in [
        "[]",
        "[1]",
        "[1, 2]",
        "[1, 2,]",
        "[1, ..xs, 3]",
        "[..xs]",
        "[1, ..xs, ..ys, 3]",
        "[[1], [2, 3]]",
        "[f x, g y]",
        "[\n  1\n  2\n]",
        "[\n  f\n    x\n  g y\n]",
        "my x = [1, 2]",
        "f [1, 2]",
        "f([1, 2], [3])",
        "([] as list int)",
    ] {
        let root = parse_file_clean(source);
        assert!(
            root.descendants()
                .any(|node| node.kind() == SyntaxKind::ListExpression),
            "{source:?}"
        );
    }
}

#[test]
fn list_spread_items_own_the_marker_and_rhs_expression() {
    let root = parse_file_clean("[1, ..xs, ..f ys, 3]");
    let spreads = root
        .descendants()
        .filter(|node| node.kind() == SyntaxKind::ListExpressionSpreadItem)
        .collect::<Vec<_>>();
    assert_eq!(spreads.len(), 2);
    for spread in spreads {
        assert_eq!(
            direct_node_kinds(&spread),
            [SyntaxKind::OperatorChain],
            "{spread:#?}"
        );
        assert_eq!(
            spread
                .descendants_with_tokens()
                .filter_map(|element| element.into_token())
                .find(|token| token.kind() == SyntaxKind::DotDot)
                .map(|token| token.kind()),
            Some(SyntaxKind::DotDot),
        );
    }
}

#[test]
fn adjacent_space_separated_expressions_form_one_ml_application_item() {
    let root = parse_file_clean("[1 2]");
    let list = root
        .descendants()
        .find(|node| node.kind() == SyntaxKind::ListExpression)
        .expect("ListExpression");
    assert_eq!(direct_node_kinds(&list), [SyntaxKind::OperatorChain]);

    let item = list.first_child().expect("one list item");
    assert_eq!(
        direct_node_kinds(&item),
        [SyntaxKind::IntegerLiteral, SyntaxKind::MlArgument]
    );
    assert_eq!(
        item.children()
            .filter(|node| node.kind() == SyntaxKind::MlArgument)
            .count(),
        1
    );
}

#[test]
fn spaced_bracket_is_an_ml_list_argument_but_adjacent_bracket_is_an_index() {
    let spaced = parse_file_clean("xs [0]");
    let spaced_chain = spaced.first_child().expect("outer OperatorChain");
    assert_eq!(
        direct_node_kinds(&spaced_chain),
        [SyntaxKind::IdentifierExpression, SyntaxKind::MlArgument]
    );
    assert!(
        spaced_chain
            .descendants()
            .any(|node| node.kind() == SyntaxKind::ListExpression)
    );
    assert!(
        !spaced_chain
            .descendants()
            .any(|node| matches!(node.kind(), SyntaxKind::IndexTail | SyntaxKind::IndexItem))
    );

    for (source, expected_outer) in [
        (
            "xs[0]",
            vec![SyntaxKind::IdentifierExpression, SyntaxKind::IndexTail],
        ),
        (
            "xs[0][1]",
            vec![
                SyntaxKind::IdentifierExpression,
                SyntaxKind::IndexTail,
                SyntaxKind::IndexTail,
            ],
        ),
    ] {
        let root = parse_file_clean(source);
        let chain = root.first_child().expect("outer OperatorChain");
        assert_eq!(direct_node_kinds(&chain), expected_outer, "{source:?}");
        assert!(
            !chain
                .descendants()
                .any(|node| node.kind() == SyntaxKind::ListExpression)
        );
    }

    let applied = parse_file_clean("f xs[0]");
    let outer = applied.first_child().expect("outer OperatorChain");
    assert_eq!(
        direct_node_kinds(&outer),
        [SyntaxKind::IdentifierExpression, SyntaxKind::MlArgument]
    );
    let argument_chain = outer
        .descendants()
        .find(|node| {
            node.kind() == SyntaxKind::OperatorChain
                && direct_node_kinds(node)
                    == [SyntaxKind::IdentifierExpression, SyntaxKind::IndexTail]
        })
        .expect("indexed ML argument");
    assert_eq!(argument_chain.to_string(), "xs[0]");
}

#[test]
fn case_and_catch_arm_bodies_accept_clean_list_expressions() {
    for (source, arm_kind) in [
        ("case x: n -> [1, 2]", SyntaxKind::CaseArm),
        ("catch x: n -> [1, 2]", SyntaxKind::CatchArm),
    ] {
        let root = parse_file_clean(source);
        let arm = root
            .descendants()
            .find(|node| node.kind() == arm_kind)
            .expect("case-like arm");
        let body = arm
            .children()
            .find(|node| node.kind() == SyntaxKind::OperatorChain)
            .expect("case-like arm body");
        let lists = body
            .children()
            .filter(|node| node.kind() == SyntaxKind::ListExpression)
            .collect::<Vec<_>>();
        assert_eq!(lists.len(), 1, "{source:?}");
        assert_eq!(lists[0].to_string(), "[1, 2]", "{source:?}");
    }
}

#[test]
fn malformed_lists_pin_delimited_recovery() {
    for (source, expected) in [
        ("[1, 2", vec![(StructuralKind::Missing, 5..5)]),
        ("[,]", vec![(StructuralKind::Missing, 1..1)]),
        ("[1)]", vec![(StructuralKind::ErrorGroup, 2..3)]),
    ] {
        let text: Arc<crate::SourceText> = Arc::from(source);
        let parsed = crate::parse_file(
            Arc::clone(&text),
            Arc::new(crate::scan_header(text)),
            Arc::new(crate::SyntaxEnvironment::empty()),
        );
        let green = parsed.green();
        assert_eq!(green.to_string(), source, "{source:?}");
        assert_eq!(structural_facts(&green), expected, "{source:?}");
    }

    let text: Arc<crate::SourceText> = Arc::from("[..]");
    let parsed = crate::parse_file(
        Arc::clone(&text),
        Arc::new(crate::scan_header(text)),
        Arc::new(crate::SyntaxEnvironment::empty()),
    );
    let green = parsed.green().clone();
    assert_eq!(green.to_string(), "[..]");
    assert_eq!(structural_facts(&green), [(StructuralKind::Missing, 3..3)]);
    let root = SyntaxNode::new_root(green);
    let spread = root
        .descendants()
        .find(|node| node.kind() == SyntaxKind::ListExpressionSpreadItem)
        .expect("spread owner");
    assert!(
        spread
            .descendants_with_tokens()
            .any(|element| element.kind() == SyntaxKind::Missing)
    );
}

#[test]
fn bracket_types_and_list_patterns_keep_their_owners() {
    let annotated = parse_file_clean("x as ['e] int");
    let annotation = annotated
        .descendants()
        .find(|node| node.kind() == SyntaxKind::TypeAnnotationTail)
        .expect("TypeAnnotationTail");
    assert_eq!(
        annotation
            .descendants_with_tokens()
            .map(|element| element.kind())
            .filter(|kind| {
                matches!(
                    kind,
                    SyntaxKind::BracketRow
                        | SyntaxKind::LBracket
                        | SyntaxKind::SigilIdentifier
                        | SyntaxKind::Identifier
                        | SyntaxKind::RBracket
                )
            })
            .collect::<Vec<_>>(),
        [
            SyntaxKind::BracketRow,
            SyntaxKind::LBracket,
            SyntaxKind::SigilIdentifier,
            SyntaxKind::RBracket,
            SyntaxKind::Identifier,
        ]
    );
    assert!(
        !annotated
            .descendants()
            .any(|node| node.kind() == SyntaxKind::ListExpression)
    );

    let pattern = parse_file_clean("case xs:\n    [a, ..rest] -> a");
    assert!(
        pattern
            .descendants()
            .any(|node| node.kind() == SyntaxKind::ListPattern)
    );
    assert!(
        pattern
            .descendants()
            .any(|node| node.kind() == SyntaxKind::ListPatternSpreadItem)
    );
    assert!(
        !pattern
            .descendants()
            .any(|node| node.kind() == SyntaxKind::ListExpression)
    );
}
