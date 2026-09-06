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
fn rule_literal_builds_interpolation_and_recovers_terminator_boundaries() {
    let source = "~\"text{value}\"tail";
    let (green, exit, remainder) = run_rule_literal(source, 0, &fence(FencePrefixPolicy::None));
    assert_eq!(exit, RuleLiteralExit::Complete);
    assert_eq!(remainder, "tail");
    assert_eq!(node_count(&green, SyntaxKind::RuleLiteralInterpolation), 1);
    assert_eq!(node_count(&green, SyntaxKind::RuleSequence), 1);
    assert_eq!(node_count(&green, SyntaxKind::RuleItem), 1);
    assert_eq!(node_count(&green, SyntaxKind::Missing), 0);

    let (green, exit, remainder) =
        run_rule_literal("~\"text{value\"tail", 0, &fence(FencePrefixPolicy::None));
    assert_eq!(exit, RuleLiteralExit::Complete);
    assert_eq!(remainder, "tail");
    assert_eq!(node_count(&green, SyntaxKind::RuleLiteralInterpolation), 1);
    assert_eq!(node_count(&green, SyntaxKind::Missing), 1);

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
fn rule_literal_interpolation_owns_rule_sequence_close_and_continuation() {
    for (source, items, strings) in [
        (r#"~"{}tail"suffix"#, 0, 0),
        (r#"~"{(a|b,c)}tail"suffix"#, 4, 0),
        (r#"~"{a="nested"}tail"suffix"#, 2, 1),
    ] {
        let (green, exit, remainder) = run_rule_literal(source, 0, &fence(FencePrefixPolicy::None));
        assert_eq!(exit, RuleLiteralExit::Complete, "{source:?}");
        assert_eq!(remainder, "suffix", "{source:?}: {}", syntax_shape(&green));
        assert_eq!(node_count(&green, SyntaxKind::RuleLiteralInterpolation), 1);
        assert_eq!(
            node_count(&green, SyntaxKind::RuleItem),
            items,
            "{source:?}"
        );
        assert_eq!(
            node_count(&green, SyntaxKind::StringLiteral),
            strings,
            "{source:?}"
        );
        assert_eq!(node_count(&green, SyntaxKind::Missing), 0, "{source:?}");
        assert_eq!(green.to_string(), &source[..source.len() - "suffix".len()]);
    }

    let source = "~\"{a \t}tail\"suffix";
    let (green, exit, remainder) = run_rule_literal(source, 0, &fence(FencePrefixPolicy::None));
    assert_eq!(exit, RuleLiteralExit::Complete);
    assert_eq!(remainder, "suffix");
    let root = SyntaxNode::new_root(green);
    let sequence = root
        .descendants()
        .find(|node| node.kind() == SyntaxKind::RuleSequence)
        .expect("RuleSequence");
    assert_eq!(sequence.text().to_string(), "a");
    let close_leading = root
        .descendants_with_tokens()
        .filter_map(|element| element.into_token())
        .find(|token| token.kind() == SyntaxKind::Whitespace)
        .expect("interpolation close leading");
    assert_eq!(close_leading.text(), " \t");
    assert_eq!(
        close_leading.parent().expect("leading parent").kind(),
        SyntaxKind::RuleLiteralInterpolation
    );
}

#[test]
fn rule_literal_sequence_uses_only_its_brace_and_outer_quote_stops() {
    for source in [
        r#"~"{a|b}tail"suffix"#,
        r#"~"{a if b}tail"suffix"#,
        r#"~"{a]b}tail"suffix"#,
    ] {
        let (green, exit, remainder) = run_rule_literal(source, 0, &fence(FencePrefixPolicy::None));
        assert_eq!(exit, RuleLiteralExit::Complete, "{source:?}");
        assert_eq!(remainder, "suffix", "{source:?}");
        assert_eq!(green.to_string(), &source[..source.len() - remainder.len()]);
        assert_eq!(node_count(&green, SyntaxKind::RuleItem), 2, "{source:?}");
        assert_eq!(node_count(&green, SyntaxKind::Error), 1, "{source:?}");
        assert_eq!(node_count(&green, SyntaxKind::Missing), 0, "{source:?}");
        let error = SyntaxNode::new_root(green)
            .descendants()
            .find(|node| node.kind() == SyntaxKind::Error)
            .expect("one interpolation-local unexpected Item");
        assert_eq!(
            error.parent().expect("Error parent").kind(),
            SyntaxKind::RuleSequence,
            "{source:?}"
        );
    }
}

#[test]
fn outer_quote_leading_stays_in_interpolation_before_missing_close() {
    let source = "~\"{a \t\"tail";
    let (green, exit, remainder) = run_rule_literal(source, 0, &fence(FencePrefixPolicy::None));
    assert_eq!(exit, RuleLiteralExit::Complete);
    assert_eq!(remainder, "tail");
    assert_eq!(green.to_string(), "~\"{a \t\"");
    assert_eq!(node_count(&green, SyntaxKind::Missing), 1);
    assert_eq!(node_count(&green, SyntaxKind::Error), 0);
    let root = SyntaxNode::new_root(green);
    let whitespace = root
        .descendants_with_tokens()
        .filter_map(|element| element.into_token())
        .find(|token| token.kind() == SyntaxKind::Whitespace)
        .expect("outer quote leading");
    assert_eq!(whitespace.text(), " \t");
    assert_eq!(
        whitespace.parent().expect("leading parent").kind(),
        SyntaxKind::RuleLiteralInterpolation
    );
    let missing = root
        .descendants()
        .find(|node| node.kind() == SyntaxKind::Missing)
        .expect("interpolation close recovery");
    assert_eq!(
        missing.parent().expect("Missing parent").kind(),
        SyntaxKind::RuleLiteralInterpolation
    );
    assert_eq!(
        root.descendants_with_tokens()
            .filter_map(|element| element.into_token())
            .filter(|token| token.kind() == SyntaxKind::RuleLiteralEnd)
            .count(),
        1
    );
}

#[test]
fn rule_literal_interpolation_orders_both_missing_slots_at_eof() {
    let source = "~\"{a";
    let (green, exit, remainder) = run_rule_literal(source, 0, &fence(FencePrefixPolicy::None));
    assert!(matches!(exit, RuleLiteralExit::Boundary(_)));
    assert_eq!(remainder, "");
    assert_eq!(green.to_string(), source);
    assert_eq!(node_count(&green, SyntaxKind::RuleLiteralInterpolation), 1);
    assert_eq!(node_count(&green, SyntaxKind::Missing), 2);
    let parents = SyntaxNode::new_root(green)
        .descendants()
        .filter(|node| node.kind() == SyntaxKind::Missing)
        .map(|node| node.parent().expect("Missing parent").kind())
        .collect::<Vec<_>>();
    assert_eq!(
        parents,
        [
            SyntaxKind::RuleLiteralInterpolation,
            SyntaxKind::RuleLiteral
        ]
    );

    let boundary = active_fence(2);
    let source = "~\"{a\n> stop\n";
    let (green, exit, remainder) = run_rule_literal(source, 0, &boundary);
    let RuleLiteralExit::Boundary(pending) = exit else {
        panic!("RuleLiteral interpolation must return the fence Item")
    };
    assert_eq!(remainder, "> stop\n");
    let FenceLineDecision::Boundary(expected_boundary) = judge_fence_line(remainder, 5, &boundary)
    else {
        panic!("fixture must denote a fence boundary")
    };
    assert_eq!(
        pending,
        Item::plain(
            LeadingTrivia::ordinary(
                vec![ordinary_trivia(TriviaKind::Newline, "\n")].into_boxed_slice()
            ),
            Payload::Boundary(expected_boundary)
        )
    );
    assert_eq!(green.to_string(), "~\"{a");
    assert_eq!(node_count(&green, SyntaxKind::Missing), 2);
}

#[test]
fn nested_capture_string_boundary_closes_every_immediate_owner() {
    let source = "~\"{a=\"unterminated";
    let (green, exit, remainder) = run_rule_literal_normalized(source, 0, None);
    let NormalizedRuleLiteralExit::Boundary(pending, line_entry) = exit else {
        panic!("nested String EOF must return the original boundary")
    };
    assert!(pending.payload_view().is_eof());
    assert_eq!(line_entry, LineEntry::InLine);
    assert_eq!(remainder, "");
    assert_eq!(green.to_string(), source);
    assert_eq!(node_count(&green, SyntaxKind::Missing), 3);
    let root = SyntaxNode::new_root(green);
    let string = root
        .descendants()
        .find(|node| node.kind() == SyntaxKind::StringLiteral)
        .expect("nested capture StringLiteral");
    assert_eq!(
        string.parent().expect("String parent").kind(),
        SyntaxKind::RuleItem
    );
    let parents = root
        .descendants()
        .filter(|node| node.kind() == SyntaxKind::Missing)
        .map(|node| node.parent().expect("Missing parent").kind())
        .collect::<Vec<_>>();
    assert_eq!(
        parents,
        [
            SyntaxKind::StringLiteral,
            SyntaxKind::RuleLiteralInterpolation,
            SyntaxKind::RuleLiteral
        ]
    );

    let boundary = active_fence(2);
    let source = "~\"{a=\"text\n> stop\n";
    let (green, exit, remainder) = run_rule_literal_normalized(source, 300, Some(&boundary));
    let NormalizedRuleLiteralExit::Boundary(pending, line_entry) = exit else {
        panic!("nested String fence must remain pending")
    };
    assert_eq!(line_entry, LineEntry::PhysicalStart);
    assert_eq!(remainder, "> stop\n");
    let FenceLineDecision::Boundary(expected_boundary) =
        judge_fence_line(remainder, 311, &boundary)
    else {
        panic!("fixture must denote a fence boundary")
    };
    assert_eq!(
        pending,
        Item::plain(
            LeadingTrivia::default(),
            Payload::Boundary(expected_boundary)
        )
    );
    assert_eq!(green.to_string(), "~\"{a=\"text\n");
    assert_eq!(node_count(&green, SyntaxKind::Missing), 3);
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
