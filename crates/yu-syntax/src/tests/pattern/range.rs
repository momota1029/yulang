use super::*;
use rowan::Language;
use std::sync::Arc;

fn parse(source: &str) -> SyntaxNode {
    let text: Arc<crate::SourceText> = Arc::from(source);
    let parsed = crate::parse_file(
        text.clone(),
        Arc::new(crate::scan_header(text)),
        Arc::new(crate::SyntaxEnvironment::empty()),
    );
    assert_eq!(parsed.green().to_string(), source, "{source:?}");
    assert!(
        parsed.syntax_diagnostics().unwrap().is_empty(),
        "{source:?}: {:#?}",
        SyntaxNode::new_root(parsed.green().clone())
    );
    assert!(structural_facts(parsed.green()).is_empty(), "{source:?}");
    SyntaxNode::new_root(parsed.green().clone())
}

#[test]
fn ranges_in_case_arms_have_literal_bounds() {
    for (pattern, bounds) in [
        ("0..10", vec!["0", "10"]),
        ("1..", vec!["1"]),
        ("..0", vec!["0"]),
        ("0x1 .. 0xA", vec!["0x1", "0xA"]),
    ] {
        let source = format!("my f n = case n:\n    {pattern} -> 1\n    _ -> 2\n");
        let root = parse(&source);
        let ranges: Vec<_> = root
            .descendants()
            .filter(|n| n.kind() == SyntaxKind::RangePattern)
            .collect();
        assert_eq!(ranges.len(), 1, "{source:?}");
        assert_eq!(ranges[0].to_string(), pattern);
        assert_eq!(
            ranges[0]
                .children()
                .filter(|n| n.kind() == SyntaxKind::IntegerPattern)
                .map(|n| n.to_string())
                .collect::<Vec<_>>(),
            bounds
        );
        assert!(
            ranges[0]
                .children_with_tokens()
                .any(|item| item.kind() == SyntaxKind::DotDot)
        );
    }
}

#[test]
fn range_patterns_compose_with_alternation_alias_and_delimiters() {
    for (pattern, ranges) in [
        ("0..5 | 10..20", vec!["0..5", "10..20"]),
        ("0..9 as d", vec!["0..9"]),
        ("(0..9, _)", vec!["0..9"]),
        ("[..0, 1.., 2..3]", vec!["..0", "1..", "2..3"]),
        ("..0 | 1.. as n", vec!["..0", "1.."]),
    ] {
        let source = format!("my f n = case n:\n    {pattern} -> 1\n    _ -> 2\n");
        let root = parse(&source);
        let found: Vec<_> = root
            .descendants()
            .filter(|n| n.kind() == SyntaxKind::RangePattern)
            .map(|n| n.to_string())
            .collect();
        assert_eq!(found, ranges, "{source:?}");
        if pattern.contains('|') {
            assert_eq!(
                root.descendants()
                    .filter(|n| n.kind() == SyntaxKind::PatternAlternationTail)
                    .count(),
                1
            );
        }
        if pattern.contains(" as ") {
            assert_eq!(
                root.descendants()
                    .filter(|n| n.kind() == SyntaxKind::PatternAliasTail)
                    .count(),
                1
            );
        }
    }
}

#[test]
fn ranges_work_in_catch_and_binding_patterns() {
    for source in [
        "my f = catch action { ..0 -> 1, 1.. -> 2 }",
        "my (0..10, _) = pair",
        "my f n = case n:\n    1 -> 1\n    ..0 -> 2\n",
    ] {
        let root = parse(source);
        assert!(
            root.descendants()
                .any(|n| n.kind() == SyntaxKind::RangePattern)
        );
    }
}

#[test]
fn range_patterns_coexist_with_an_expression_range_operator() {
    let source = "infix (..) 50 51 = f\nmy a = 0..10\nmy f n = case n:\n    1 -> 1\n    ..0 -> 2\n";
    let root = parse(source);
    assert_eq!(
        root.descendants()
            .filter(|node| node.kind() == SyntaxKind::RangePattern)
            .count(),
        1
    );
    assert!(
        root.descendants()
            .any(|node| node.kind() == SyntaxKind::InfixOperatorUse && node.to_string() == "..")
    );
}

#[test]
fn open_range_hands_the_next_item_back() {
    let (green, exit, _) =
        run_pattern_normalized("1..  next", 0, LineEntry::InLine, None, PATTERN_STOP_ITEM);
    assert_eq!(green.to_string(), "1..");
    let item = match exit {
        NormalizedExit::Complete(Err(Either::Left(item)), _) => item,
        _ => panic!("expected the following item"),
    };
    assert_eq!(item.payload_view().spelling(), Some("next"));
    assert!(item.leading_view().has_ordinary_trivia());
}

#[test]
fn range_kind_round_trips_through_rowan() {
    let kind = SyntaxKind::RangePattern;
    assert_eq!(
        <crate::YulangLanguage as Language>::kind_from_raw(kind.into()),
        kind
    );
}

#[test]
fn spread_and_bare_dotdot_keep_the_original_cst() {
    for (source, expected) in [
        (
            "[x, ..rest]",
            "Root@0..11\n  Pattern@0..11\n    ListPattern@0..11\n      LBracket@0..1 \"[\"\n      Pattern@1..2\n        IdentifierPattern@1..2\n          Identifier@1..2 \"x\"\n      Comma@2..3 \",\"\n      Whitespace@3..4 \" \"\n      ListPatternSpreadItem@4..10\n        DotDot@4..6 \"..\"\n        Pattern@6..10\n          IdentifierPattern@6..10\n            Identifier@6..10 \"rest\"\n      RBracket@10..11 \"]\"\n",
        ),
        (
            "{x, ..rest}",
            "Root@0..11\n  Pattern@0..11\n    RecordPattern@0..11\n      LBrace@0..1 \"{\"\n      RecordPatternField@1..2\n        Identifier@1..2 \"x\"\n      Comma@2..3 \",\"\n      Whitespace@3..4 \" \"\n      RecordPatternSpreadItem@4..10\n        DotDot@4..6 \"..\"\n        Pattern@6..10\n          IdentifierPattern@6..10\n            Identifier@6..10 \"rest\"\n      RBrace@10..11 \"}\"\n",
        ),
        (
            ".._",
            "Root@0..3\n  Pattern@0..3\n    Error@0..2 \"..\"\n    IdentifierPattern@2..3\n      Identifier@2..3 \"_\"\n",
        ),
        ("..", "Root@0..2\n  Pattern@0..2\n    Error@0..2 \"..\"\n"),
    ] {
        let (green, _) = run_pattern(source);
        assert_eq!(
            format!("{:#?}", SyntaxNode::new_root(green.clone())),
            expected,
            "{source:?}"
        );
        if source.starts_with('[') || source.starts_with('{') {
            assert!(structural_facts(&green).is_empty(), "{source:?}");
        }
    }
    for (source, kind) in [
        ("[x, .._]", SyntaxKind::ListPatternSpreadItem),
        ("{x, .._}", SyntaxKind::RecordPatternSpreadItem),
    ] {
        let (green, _) = run_pattern(source);
        assert_eq!(green.to_string(), source);
        assert!(structural_facts(&green).is_empty());
        let root = SyntaxNode::new_root(green);
        assert_eq!(root.descendants().filter(|n| n.kind() == kind).count(), 1);
        assert!(
            !root
                .descendants()
                .any(|n| n.kind() == SyntaxKind::RangePattern)
        );
    }
}
