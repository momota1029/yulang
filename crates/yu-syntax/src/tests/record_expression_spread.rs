use crate::tests::support::*;
use std::sync::Arc;

fn parse_file(source: &str) -> crate::ParsedFile {
    let text: Arc<crate::SourceText> = Arc::from(source);
    let parsed = crate::parse_file(
        Arc::clone(&text),
        Arc::new(crate::scan_header(text)),
        Arc::new(crate::SyntaxEnvironment::empty()),
    );
    assert_eq!(parsed.green().to_string(), source, "{source:?}");
    parsed
}

fn parse_file_clean(source: &str) -> SyntaxNode {
    let parsed = parse_file(source);
    assert!(
        parsed.syntax_diagnostics().unwrap().is_empty(),
        "{source:?}"
    );
    let green = parsed.green().clone();
    assert!(structural_facts(&green).is_empty(), "{source:?}");
    let root = SyntaxNode::new_root(green);
    assert!(
        !root.descendants_with_tokens().any(|element| matches!(
            element.kind(),
            SyntaxKind::Error | SyntaxKind::Missing | SyntaxKind::Invalid
        )),
        "{source:?}"
    );
    root
}

#[test]
fn brace_expression_spreads_accept_all_item_positions_and_layout() {
    for source in [
        "{x: 1, ..rest}",
        "{..rest, x: 1}",
        "{x: 1, y: 2, ..rest}",
        "{x, ..rest}",
        "{..rest}",
        "infix (..) 50 51 = range\n{..(1..3)}",
        "{\n  x: 1,\n  ..rest\n}",
        "{\r\n  x: 1,\r\n  ..rest,\r\n}",
        "{\n  x: 1\n  ..rest\n}",
        "{x: 1, ..rest,}",
    ] {
        parse_file_clean(source);
    }
}

#[test]
fn brace_spread_items_own_the_marker_and_rhs_expression() {
    let root = parse_file_clean("{x: 1, ..rest, ..f ys}");
    let block = root
        .descendants()
        .find(|node| node.kind() == SyntaxKind::BracedStatementBlockExpression)
        .expect("brace expression");
    assert_eq!(
        block.children().map(|node| node.kind()).collect::<Vec<_>>(),
        [
            SyntaxKind::Statement,
            SyntaxKind::BlockStatementSeparator,
            SyntaxKind::RecordExpressionSpreadItem,
            SyntaxKind::BlockStatementSeparator,
            SyntaxKind::RecordExpressionSpreadItem,
        ]
    );
    let spreads = block
        .children()
        .filter(|node| node.kind() == SyntaxKind::RecordExpressionSpreadItem)
        .collect::<Vec<_>>();
    for (spread, rhs) in spreads.iter().zip(["rest", "f ys"]) {
        assert_eq!(spread.to_string(), format!("..{rhs}"));
        assert_eq!(
            spread
                .children_with_tokens()
                .map(|child| child.kind())
                .collect::<Vec<_>>(),
            [SyntaxKind::DotDot, SyntaxKind::OperatorChain]
        );
        assert_eq!(spread.first_child().unwrap().to_string(), rhs);
    }
    assert!(
        spreads[1]
            .descendants()
            .any(|node| node.kind() == SyntaxKind::MlArgument)
    );
}

#[test]
fn range_and_suffix_operators_keep_their_meaning_in_and_outside_spread_rhs() {
    let root = parse_file_clean(
        "infix (..) 50 51 = range\nsuffix (..) 60 = from\n\
         my r = 1..3\nxs[0]..\n{..(1..3), ..xs[0]..}",
    );
    for (kind, expected) in [
        (SyntaxKind::InfixOperatorUse, 2),
        (SyntaxKind::SuffixOperatorUse, 2),
        (SyntaxKind::RecordExpressionSpreadItem, 2),
    ] {
        assert_eq!(
            root.descendants()
                .filter(|node| node.kind() == kind)
                .count(),
            expected
        );
    }
    let range_spread = root
        .descendants()
        .find(|node| node.kind() == SyntaxKind::RecordExpressionSpreadItem)
        .unwrap();
    assert_eq!(range_spread.to_string(), "..(1..3)");
    assert!(
        range_spread
            .descendants()
            .any(|node| node.kind() == SyntaxKind::InfixOperatorUse)
    );
}

#[test]
fn brace_item_start_spread_wins_over_a_declared_prefix_operator() {
    let root = parse_file_clean("prefix (..) 60 = prefix_range\n..rest\n{..rest}");
    assert_eq!(
        root.descendants()
            .filter(|node| node.kind() == SyntaxKind::PrefixOperatorUse)
            .count(),
        1
    );
    assert_eq!(
        root.descendants()
            .filter(|node| node.kind() == SyntaxKind::RecordExpressionSpreadItem)
            .count(),
        1
    );
}

#[test]
fn statement_only_braces_keep_their_existing_cst() {
    for (source, expected) in [
        ("{x: 1}", vec![SyntaxKind::Statement]),
        ("{x}", vec![SyntaxKind::Statement]),
        ("{;}", vec![SyntaxKind::BlockStatementSeparator]),
    ] {
        let root = parse_file_clean(source);
        let block = root
            .descendants()
            .find(|node| node.kind() == SyntaxKind::BracedStatementBlockExpression)
            .unwrap();
        assert_eq!(
            block.children().map(|node| node.kind()).collect::<Vec<_>>(),
            expected
        );
        assert!(
            !block
                .descendants()
                .any(|node| node.kind() == SyntaxKind::RecordExpressionSpreadItem)
        );
        if source == "{x: 1}" {
            assert_eq!(
                block
                    .descendants()
                    .filter(|node| node.kind() == SyntaxKind::ColonApplicationTail)
                    .count(),
                1
            );
        }
    }
}

#[test]
fn brace_spreads_reuse_delimited_rhs_recovery_and_brace_item_retry() {
    use crate::structural_diagnostic::StructuralKind::{ErrorGroup, Missing};
    for (source, expected) in [
        ("{..}", vec![(Missing, 3..3)]),
        ("{.., x}", vec![(Missing, 3..3)]),
        ("{..@ rest}", vec![(ErrorGroup, 3..4)]),
        ("{@ ..rest}", vec![(ErrorGroup, 1..2)]),
        // Like the existing brace separator pins, Missing starts at the gap's
        // pending leading trivia, before the next item's marker.
        ("{..rest ..more}", vec![(Missing, 7..7)]),
    ] {
        let green = parse_file(source).green().clone();
        assert_eq!(structural_facts(&green), expected, "{source:?}");
        let root = SyntaxNode::new_root(green);
        assert!(
            root.descendants()
                .any(|node| node.kind() == SyntaxKind::RecordExpressionSpreadItem),
            "{source:?}"
        );
        let block = root
            .descendants()
            .find(|node| node.kind() == SyntaxKind::BracedStatementBlockExpression)
            .unwrap();
        assert_eq!(block.last_token().unwrap().kind(), SyntaxKind::RBrace);
    }
}
