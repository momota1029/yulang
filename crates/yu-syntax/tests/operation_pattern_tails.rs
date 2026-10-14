use std::sync::Arc;

use yu_syntax::{
    ParsedFile, SyntaxDiagnosticCause, SyntaxEnvironment, SyntaxKind, SyntaxNode, parse_file,
    scan_header,
};

fn parse(source: &str) -> ParsedFile {
    let source: Arc<str> = Arc::from(source);
    let header = Arc::new(scan_header(Arc::clone(&source)));
    let parsed = parse_file(source.clone(), header, Arc::new(SyntaxEnvironment::empty()));
    assert_eq!(parsed.green().to_string(), source.as_ref());
    parsed
}

fn nodes(parsed: &ParsedFile, kind: SyntaxKind) -> Vec<SyntaxNode> {
    SyntaxNode::new_root(parsed.green().clone())
        .descendants()
        .filter(|node| node.kind() == kind)
        .collect()
}

fn direct_kinds(node: &SyntaxNode) -> Vec<SyntaxKind> {
    node.children().map(|child| child.kind()).collect()
}

#[test]
fn qualified_empty_operation_and_value_arm_keep_handler_comma() {
    let parsed = parse("catch signal::ping() { signal::ping(), k -> k 1, v -> v }");
    assert!(parsed.syntax_diagnostics().unwrap().is_empty());
    let calls = nodes(&parsed, SyntaxKind::PatternCallTail);
    assert_eq!(calls.len(), 1);
    assert_eq!(calls[0].text().to_string(), "()");
    assert!(calls[0].children().next().is_none());
    let patterns = nodes(&parsed, SyntaxKind::Pattern);
    assert_eq!(
        direct_kinds(&patterns[0]),
        [
            SyntaxKind::IdentifierPattern,
            SyntaxKind::PatternPathTail,
            SyntaxKind::PatternCallTail
        ]
    );
    assert_eq!(nodes(&parsed, SyntaxKind::CatchArm).len(), 2);
    assert_eq!(patterns[1].text().to_string(), " k");
    let binding = patterns[1].children().next().unwrap();
    assert_eq!(binding.kind(), SyntaxKind::IdentifierPattern);
    let leading = binding.first_token().unwrap();
    assert_eq!(leading.kind(), SyntaxKind::Whitespace);
    assert_eq!(leading.text(), " ");
    assert_eq!(patterns[2].text().to_string(), "v");
}

#[test]
fn payload_commas_and_nested_patterns_belong_to_call() {
    let parsed = parse("catch action { A(x, B(y), [z]), k -> k, v -> v }");
    assert!(parsed.syntax_diagnostics().unwrap().is_empty());
    let calls = nodes(&parsed, SyntaxKind::PatternCallTail);
    assert_eq!(calls.len(), 2);
    assert_eq!(calls[0].text().to_string(), "(x, B(y), [z])");
    assert_eq!(
        calls[0]
            .children()
            .filter(|n| n.kind() == SyntaxKind::Pattern)
            .count(),
        3
    );
    assert_eq!(nodes(&parsed, SyntaxKind::CatchArm).len(), 2);
}

#[test]
fn fixed_tails_chain_after_every_admitted_head_and_alias() {
    for head in ["A", "_", "$a", "(A)", "A as b", "A(x)"] {
        let source = format!("catch action {{ {head}::B(x)(y), k -> k }}");
        let parsed = parse(&source);
        assert!(parsed.syntax_diagnostics().unwrap().is_empty(), "{source}");
        let pattern = nodes(&parsed, SyntaxKind::Pattern).remove(0);
        let kinds = direct_kinds(&pattern);
        assert_eq!(
            &kinds[kinds.len() - 3..],
            [
                SyntaxKind::PatternPathTail,
                SyntaxKind::PatternCallTail,
                SyntaxKind::PatternCallTail,
            ]
        );
    }
    for member in ["_", "as"] {
        let parsed = parse(&format!("catch action {{ A::{member}(), k -> k }}"));
        assert!(parsed.syntax_diagnostics().unwrap().is_empty());
    }
}

#[test]
fn fixed_tails_bind_inside_ml_argument_but_spaced_open_is_ml() {
    let parsed = parse("cast((f x::Y(y))): T;");
    assert!(parsed.syntax_diagnostics().unwrap().is_empty());
    let ml = nodes(&parsed, SyntaxKind::PatternMlApplicationTail);
    assert_eq!(ml.len(), 1);
    let argument = ml[0].children().next().unwrap();
    assert_eq!(
        direct_kinds(&argument),
        [
            SyntaxKind::IdentifierPattern,
            SyntaxKind::PatternPathTail,
            SyntaxKind::PatternCallTail,
        ]
    );
    let parsed = parse("cast((A (x))): T;");
    assert!(parsed.syntax_diagnostics().unwrap().is_empty());
    assert!(nodes(&parsed, SyntaxKind::PatternCallTail).is_empty());
    assert_eq!(
        nodes(&parsed, SyntaxKind::PatternMlApplicationTail).len(),
        1
    );
}

#[test]
fn path_retry_keeps_native_leading_and_generic_error() {
    let parsed = parse("catch action { A::@ B(), k -> k }");
    let path = nodes(&parsed, SyntaxKind::PatternPathTail).remove(0);
    assert_eq!(path.text().to_string(), "::@ B");
    let tokens: Vec<_> = path
        .children_with_tokens()
        .filter_map(|child| child.into_token())
        .collect();
    assert_eq!(
        tokens
            .iter()
            .map(|token| (token.kind(), token.text()))
            .collect::<Vec<_>>(),
        [
            (SyntaxKind::ColonColon, "::"),
            (SyntaxKind::Error, "@"),
            (SyntaxKind::Whitespace, " "),
            (SyntaxKind::Identifier, "B"),
        ]
    );
    assert!(path.children().next().is_none());
    assert_eq!(nodes(&parsed, SyntaxKind::PatternCallTail).len(), 1);
    let diagnostics = parsed.syntax_diagnostics().unwrap();
    assert_eq!(diagnostics.len(), 1);
    let SyntaxDiagnosticCause::Structural(recovery) = diagnostics[0].cause() else {
        panic!("path recovery must retain structural publication");
    };
    assert_eq!(recovery.parent(), SyntaxKind::PatternPathTail);
    assert!(recovery.expectations().is_none());
}

#[test]
fn missing_members_leave_sibling_tails_and_handler_comma() {
    for (head, paths, calls) in [("A::", 1, 0), ("A::::B", 2, 0), ("A::()", 1, 1)] {
        let parsed = parse(&format!("catch action {{ {head}, k -> k }}"));
        assert_eq!(nodes(&parsed, SyntaxKind::PatternPathTail).len(), paths);
        assert_eq!(nodes(&parsed, SyntaxKind::PatternCallTail).len(), calls);
        let missing = nodes(&parsed, SyntaxKind::Missing);
        assert_eq!(missing.len(), 1);
        assert_eq!(
            missing[0].parent().unwrap().kind(),
            SyntaxKind::PatternPathTail
        );
        assert_eq!(nodes(&parsed, SyntaxKind::CatchArm).len(), 1);
    }
}

#[test]
fn call_close_recovery_uses_generic_structural_fallback() {
    let parsed = parse("catch action { A(x");
    let diagnostics = parsed.syntax_diagnostics().unwrap();
    let closes: Vec<_> = diagnostics
        .iter()
        .filter_map(|diagnostic| match diagnostic.cause() {
            SyntaxDiagnosticCause::Structural(recovery)
                if recovery.parent() == SyntaxKind::PatternCallTail =>
            {
                Some(recovery)
            }
            _ => None,
        })
        .collect();
    assert_eq!(closes.len(), 1);
    assert!(closes[0].expectations().is_none());
}

#[test]
fn call_separator_recovery_remains_generic() {
    for source in [
        "catch action { A(x()y), k -> k }",
        "catch action { A(x @ y), k -> k }",
    ] {
        let parsed = parse(source);
        let diagnostics = parsed.syntax_diagnostics().unwrap();
        let separators: Vec<_> = diagnostics
            .iter()
            .filter_map(|diagnostic| match diagnostic.cause() {
                SyntaxDiagnosticCause::Structural(recovery)
                    if recovery.parent() == SyntaxKind::PatternCallTail =>
                {
                    Some(recovery)
                }
                _ => None,
            })
            .collect();
        assert_eq!(separators.len(), 1, "{source}");
        assert!(separators[0].expectations().is_none());
        assert_eq!(nodes(&parsed, SyntaxKind::CatchArm).len(), 1);
    }
}

#[test]
fn nested_call_hands_carried_list_close_back_to_list() {
    let parsed = parse("catch action { A([B(x  ]), k -> k }");
    let missing = nodes(&parsed, SyntaxKind::Missing);
    assert_eq!(missing.len(), 1);
    assert_eq!(
        missing[0].parent().unwrap().kind(),
        SyntaxKind::PatternCallTail
    );
    let calls = nodes(&parsed, SyntaxKind::PatternCallTail);
    assert_eq!(calls.len(), 2);
    assert_eq!(calls[1].text().to_string(), "(x");
    assert_eq!(
        nodes(&parsed, SyntaxKind::ListPattern)[0]
            .text()
            .to_string(),
        "[B(x  ]"
    );
    assert_eq!(nodes(&parsed, SyntaxKind::CatchArm).len(), 1);
}
