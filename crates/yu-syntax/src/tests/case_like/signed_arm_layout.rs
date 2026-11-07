use super::*;

const OPERATORS: &str = "infix (-) 50 51 = sub\nprefix (-) 80 = neg\n\
    infix (+) 50 51 = add\ninfix (..) 45 46 = range\nsuffix (..) 80 = from\n\
    infix (|) 10 11 = pipe\n";

fn clean(source: &str) -> SyntaxNode {
    case_like_literal_production(&format!("{OPERATORS}{source}"))
}

fn arms(root: &SyntaxNode) -> Vec<SyntaxNode> {
    root.descendants()
        .filter(|node| matches!(node.kind(), SyntaxKind::CaseArm | SyntaxKind::CatchArm))
        .collect()
}

fn patterns(arms: &[SyntaxNode]) -> Vec<String> {
    arms.iter()
        .map(|arm| arm.first_child().unwrap().to_string())
        .collect()
}

#[test]
fn later_signed_arm_patterns_keep_first_arm_cst() {
    use SyntaxKind::*;
    // The integer is one signed token, including when it starts a range or
    // alternation. The arm still owns Pattern, Arrow and body directly.
    for (pattern, children, integers) in [
        ("-1", vec![IntegerPattern], vec!["-1"]),
        ("-1..5", vec![RangePattern], vec!["-1", "5"]),
        ("..-1", vec![RangePattern], vec!["-1"]),
        (
            "-1 | 1",
            vec![IntegerPattern, PatternAlternationTail],
            vec!["-1", "1"],
        ),
        ("-0xA", vec![IntegerPattern], vec!["-0xA"]),
        ("-1_000", vec![IntegerPattern], vec!["-1_000"]),
    ] {
        for (head, close) in [
            ("case n:", ""),
            ("case:", ""),
            ("catch n:", ""),
            ("catch n {", "}\n"),
        ] {
            let source = format!("{head}\n    0 -> 1\n    {pattern} -> 2\n{close}");
            let root = clean(&source);
            let arms = arms(&root);
            assert_eq!(patterns(&arms), ["0", pattern], "{source:?}");
            assert_eq!(
                arms[1]
                    .children()
                    .map(|node| node.kind())
                    .collect::<Vec<_>>(),
                [Pattern, OperatorChain],
                "{source:?}"
            );
            assert!(
                arms[1]
                    .children_with_tokens()
                    .any(|child| child.kind() == Arrow)
            );
            let pat = arms[1].first_child().unwrap();
            assert_eq!(
                pat.children().map(|node| node.kind()).collect::<Vec<_>>(),
                children,
                "{source:?}"
            );
            assert_eq!(
                pat.descendants_with_tokens()
                    .filter_map(|child| child.into_token())
                    .filter(|token| token.kind() == Integer)
                    .map(|token| token.text().to_owned())
                    .collect::<Vec<_>>(),
                integers,
                "{source:?}"
            );
            assert_eq!(arms[0].last_child().unwrap().to_string(), "1");
            assert_eq!(arms[1].last_child().unwrap().to_string(), "2");
        }
    }
}

#[test]
fn three_signed_arms_keep_separate_patterns_and_bodies() {
    for head in ["case n:", "catch n:"] {
        let source = format!("{head}\n    0 -> 1\n    -1 -> 2\n    -2 -> 3\n");
        let root = clean(&source);
        let arms = arms(&root);
        assert_eq!(patterns(&arms), ["0", "-1", "-2"]);
        assert_eq!(
            arms.iter()
                .map(|arm| arm.last_child().unwrap().to_string())
                .collect::<Vec<_>>(),
            ["1", "2", "3"]
        );
    }
}

#[test]
fn signed_arm_after_multiline_body_keeps_body_ownership() {
    for head in ["case n:", "catch n:"] {
        for (body, kind) in [
            (" f\n        x", SyntaxKind::OperatorChain),
            (
                "\n        my a = 1\n        a",
                SyntaxKind::IndentedStatementBlock,
            ),
        ] {
            let source = format!("{head}\n    0 ->{body}\n    -1 -> 2\n");
            let root = clean(&source);
            let arms = arms(&root);
            assert_eq!(patterns(&arms), ["0", "-1"], "{source:?}");
            let first_body = arms[0].last_child().unwrap();
            assert_eq!(first_body.kind(), kind);
            assert_eq!(first_body.to_string().trim(), body.trim());
            assert_eq!(arms[1].last_child().unwrap().to_string(), "2");
        }
    }
}

#[test]
fn deeper_operator_line_keeps_continuing_arm_body() {
    for head in ["case n:", "catch n:"] {
        for subtraction in ["- 2", "- x", "-2"] {
            let source = format!("{head}\n    0 -> 1\n        {subtraction}\n    -1 -> 2\n");
            let root = clean(&source);
            let arms = arms(&root);
            assert_eq!(patterns(&arms), ["0", "-1"]);
            let body = arms[0].last_child().unwrap();
            assert_eq!(body.to_string(), format!("1\n        {subtraction}"));
            assert_eq!(
                body.children().map(|node| node.kind()).collect::<Vec<_>>(),
                if subtraction == "-2" {
                    // With no space after the sign, expression operator
                    // selection keeps this as a prefix ML argument.
                    vec![SyntaxKind::IntegerLiteral, SyntaxKind::MlArgument]
                } else {
                    vec![
                        SyntaxKind::IntegerLiteral,
                        SyntaxKind::InfixOperatorUse,
                        if subtraction == "- x" {
                            SyntaxKind::IdentifierExpression
                        } else {
                            SyntaxKind::IntegerLiteral
                        },
                    ]
                },
                "{source:?}"
            );
        }
    }
}

#[test]
fn parenthesized_and_first_signed_arm_controls_keep_parsing() {
    for head in ["case n:", "catch n:"] {
        for pattern in ["-1", "-1..5", "..-1", "-1 | 1"] {
            let root = clean(&format!("{head}\n    {pattern} -> 2\n"));
            assert_eq!(patterns(&arms(&root)), [pattern]);
        }
        let root = clean(&format!("{head}\n    0 -> 1\n    (-1) -> 2\n"));
        let arms = arms(&root);
        assert_eq!(patterns(&arms), ["0", "(-1)"]);
        assert_eq!(
            arms[1].first_child().unwrap().first_child().unwrap().kind(),
            SyntaxKind::ParenthesizedPattern
        );
    }
}

#[test]
fn plus_and_spaced_minus_stay_errors_in_first_and_later_arms() {
    use std::sync::Arc;
    // These were errors before WP-15. Neither spelling is a signed Pattern.
    for head in ["case n:", "catch n:"] {
        for pattern in ["+1", "- 1"] {
            for preceding in ["", "    0 -> 1\n"] {
                let source = format!("{OPERATORS}{head}\n{preceding}    {pattern} -> 2\n");
                let text: Arc<crate::SourceText> = Arc::from(source.as_str());
                let parsed = crate::parse_file(
                    text.clone(),
                    Arc::new(crate::scan_header(text)),
                    Arc::new(crate::SyntaxEnvironment::empty()),
                );
                assert_eq!(parsed.green().to_string(), source);
                assert!(
                    !parsed.syntax_diagnostics().unwrap().is_empty(),
                    "{source:?}"
                );
                assert!(!structural_facts(parsed.green()).is_empty(), "{source:?}");
            }
        }
    }
}

#[test]
fn same_line_minus_without_an_operator_keeps_malformed_recovery() {
    use std::sync::Arc;
    // WP-15 admits a new arm at a newline, not a same-line missing separator.
    for source in [
        "case n: 0 -> 1 -1 -> 2",
        "case n:\n    0 -> 1 -1 -> 2",
        "catch n { 0 -> 1 -1 -> 2 }",
        "catch n:\n    0 -> 1 -1 -> 2",
    ] {
        let text: Arc<crate::SourceText> = Arc::from(source);
        let parsed = crate::parse_file(
            text.clone(),
            Arc::new(crate::scan_header(text)),
            Arc::new(crate::SyntaxEnvironment::empty()),
        );
        assert_eq!(parsed.green().to_string(), source);
        assert!(!parsed.syntax_diagnostics().unwrap().is_empty());
        let root = SyntaxNode::new_root(parsed.green().clone());
        assert_eq!(patterns(&arms(&root)), ["0"], "{source:?}");
        assert!(
            !root.descendants().any(|node| {
                node.kind() == SyntaxKind::IntegerPattern && node.to_string() == "-1"
            })
        );
    }
}

#[test]
fn same_indent_statement_minus_still_starts_a_statement() {
    for first in ["my a = 1", "1"] {
        let root = clean(&format!("{first}\n-1\n"));
        let last = root.children().last().unwrap();
        assert_eq!(last.kind(), SyntaxKind::OperatorChain);
        assert_eq!(last.to_string(), "-1");
        assert_eq!(
            last.children().map(|node| node.kind()).collect::<Vec<_>>(),
            [SyntaxKind::PrefixOperatorUse, SyntaxKind::IntegerLiteral]
        );
    }
}

#[test]
fn if_for_and_with_body_controls_keep_statement_layout() {
    for source in [
        "if c:\n    1\n    -1\nelsif d:\n    2\n    -2\nelse:\n    3\n    -3\n",
        "for x in xs:\n    1\n    -1\n",
        "f with:\n    1\n    -1\n",
    ] {
        let root = clean(source);
        assert!(arms(&root).is_empty());
        let blocks = root
            .descendants()
            .filter(|node| node.kind() == SyntaxKind::IndentedStatementBlock)
            .collect::<Vec<_>>();
        assert_eq!(blocks.len(), if source.starts_with("if") { 3 } else { 1 });
        for block in blocks {
            let statements = block
                .children()
                .filter(|node| node.kind() == SyntaxKind::Statement)
                .collect::<Vec<_>>();
            assert_eq!(statements.len(), 2, "{source:?}");
            assert!(
                statements[1]
                    .descendants()
                    .any(|node| node.kind() == SyntaxKind::PrefixOperatorUse)
            );
        }
    }
}
