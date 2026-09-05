use super::*;

#[test]
fn expression_rule_literal_owns_raw_text_and_both_lazy_capture_forms() {
    let source = "~\"a\\b:name:{x=y\"z\r\nw}\"tail";
    let (green, exit, remainder) = run_rule_literal(source, 0, &fence(FencePrefixPolicy::None));
    assert_eq!(exit, RuleLiteralExit::Complete);
    assert_eq!(remainder, "tail");
    assert_eq!(node_count(&green, SyntaxKind::RuleLiteral), 1);
    assert_eq!(node_count(&green, SyntaxKind::RuleLazyCapture), 2);
    assert_eq!(node_count(&green, SyntaxKind::Missing), 0);
    assert_eq!(
        node_texts(&green, SyntaxKind::RuleLazyCapture),
        [":name", ":{x=y\"z\r\nw}"]
    );
    assert!(syntax_tokens(&green).contains(&(SyntaxKind::RuleLiteralText, "a\\b".to_owned())));
}

#[test]
fn rule_literal_defers_interpolation_and_recovers_terminator_boundaries() {
    let source = "~\"text{rule}\"tail";
    let start = source.as_ptr();
    let (green, exit, remainder) = run_rule_literal(source, 0, &fence(FencePrefixPolicy::None));
    let RuleLiteralExit::DeferredInterpolation(open) = exit else {
        panic!("plain open brace stays deferred")
    };
    assert_eq!(token_text(&open), "{");
    assert_eq!(remainder, "rule}\"tail");
    assert_eq!(
        remainder.as_ptr(),
        start.wrapping_add(source.len() - remainder.len())
    );
    assert_eq!(node_count(&green, SyntaxKind::RuleLiteralInterpolation), 0);

    let (green, exit, remainder) =
        run_rule_literal("~\"unterminated", 0, &fence(FencePrefixPolicy::None));
    assert!(matches!(
        exit,
        RuleLiteralExit::Boundary(item) if item.payload_view().is_boundary()
    ));
    assert_eq!(remainder, "");
    assert_eq!(node_count(&green, SyntaxKind::Missing), 1);

    let boundary = active_fence(2);
    let source = "~\"α\n> stop\n";
    let (green, exit, remainder) = run_rule_literal(source, 0, &boundary);
    let RuleLiteralExit::Boundary(pending) = exit else {
        panic!("fence line remains pending")
    };
    assert_eq!(remainder, "> stop\n");
    assert_eq!(pending, expected_pending(remainder, 5, &boundary));
    assert_eq!(node_count(&green, SyntaxKind::Missing), 1);
}

#[test]
fn rule_literal_fenced_crlf_utf8_keeps_fragment_order_in_text_and_capture() {
    let boundary = active_fence(2);
    let source = "~\"α\r\n> > β:{x=y\r\n> > γ}\"tail";
    let (green, exit, remainder) = run_rule_literal(source, 0, &boundary);
    assert_eq!(exit, RuleLiteralExit::Complete);
    assert_eq!(remainder, "tail");
    assert_eq!(node_count(&green, SyntaxKind::Missing), 0);
    assert_eq!(
        syntax_tokens(&green),
        [
            (SyntaxKind::RuleLiteralStart, "~\"".to_owned()),
            (SyntaxKind::RuleLiteralText, "α\r\n".to_owned()),
            (SyntaxKind::YmQuotePrefix, "> > ".to_owned()),
            (SyntaxKind::RuleLiteralText, "β".to_owned()),
            (SyntaxKind::RuleLiteralColon, ":".to_owned()),
            (SyntaxKind::RuleLiteralOpenBrace, "{".to_owned()),
            (SyntaxKind::RuleLiteralText, "x=y\r\n".to_owned()),
            (SyntaxKind::YmQuotePrefix, "> > ".to_owned()),
            (SyntaxKind::RuleLiteralText, "γ".to_owned()),
            (SyntaxKind::RuleLiteralCloseBrace, "}".to_owned()),
            (SyntaxKind::RuleLiteralEnd, "\"".to_owned()),
        ]
    );
}

#[test]
fn rule_lazy_capture_missing_slots_preserve_outer_quote_or_boundary() {
    let boundary = fence(FencePrefixPolicy::None);
    let (green, exit, remainder) = run_rule_literal("~\":\"tail", 0, &boundary);
    assert_eq!(exit, RuleLiteralExit::Complete);
    assert_eq!(remainder, "tail");
    assert_eq!(node_count(&green, SyntaxKind::Missing), 1);
    assert_eq!(node_texts(&green, SyntaxKind::RuleLazyCapture), [":"]);

    let (green, exit, remainder) = run_rule_literal("~\":{x", 0, &boundary);
    assert!(matches!(exit, RuleLiteralExit::Boundary(_)));
    assert_eq!(remainder, "");
    assert_eq!(node_count(&green, SyntaxKind::Missing), 2);
    let kinds = SyntaxNode::new_root(green)
        .descendants()
        .filter(|node| node.kind() == SyntaxKind::Missing)
        .map(|node| node.parent().unwrap().kind())
        .collect::<Vec<_>>();
    assert_eq!(
        kinds,
        [SyntaxKind::RuleLazyCapture, SyntaxKind::RuleLiteral]
    );
}
