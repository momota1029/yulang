use super::*;

fn pattern_node(green: GreenNode) -> SyntaxNode {
    SyntaxNode::new_root(green)
        .children()
        .find(|node| node.kind() == SyntaxKind::Pattern)
        .expect("Pattern")
}

#[test]
fn standalone_patterns_emit_atomic_primaries_without_operator_chains() {
    for (source, child, token) in [
        ("x", SyntaxKind::IdentifierPattern, SyntaxKind::Identifier),
        ("_", SyntaxKind::IdentifierPattern, SyntaxKind::Identifier),
        (
            "_bar",
            SyntaxKind::IdentifierPattern,
            SyntaxKind::SigilIdentifier,
        ),
        (
            "$x",
            SyntaxKind::IdentifierPattern,
            SyntaxKind::SigilIdentifier,
        ),
        (
            "&x",
            SyntaxKind::IdentifierPattern,
            SyntaxKind::SigilIdentifier,
        ),
        (
            "'x",
            SyntaxKind::IdentifierPattern,
            SyntaxKind::SigilIdentifier,
        ),
        ("0", SyntaxKind::IntegerPattern, SyntaxKind::Integer),
        ("42", SyntaxKind::IntegerPattern, SyntaxKind::Integer),
    ] {
        let (green, exit) = run_pattern(source);
        assert_eq!(green.to_string(), source, "{source:?}");
        assert!(matches!(exit, Err(Either::Right(_))), "{source:?}");
        let pattern = pattern_node(green);
        let primary = pattern.children().next().expect("Pattern primary");
        assert_eq!(primary.kind(), child, "{source:?}");
        assert_eq!(primary.first_token().map(|token| token.kind()), Some(token));
        assert!(
            !pattern
                .descendants()
                .any(|node| node.kind() == SyntaxKind::OperatorChain),
            "{source:?}"
        );
    }
}

#[test]
fn standalone_patterns_keep_symbols_and_parenthesized_layout_local() {
    let (green, exit) = run_pattern(":foo");
    assert_eq!(green.to_string(), ":foo");
    assert!(matches!(exit, Err(Either::Right(_))));
    let pattern = pattern_node(green);
    let symbol = pattern
        .children()
        .find(|node| node.kind() == SyntaxKind::SymbolPattern)
        .expect("SymbolPattern");
    assert_eq!(
        symbol
            .children_with_tokens()
            .filter_map(|element| element.into_token())
            .map(|token| token.kind())
            .collect::<Vec<_>>(),
        [SyntaxKind::Colon, SyntaxKind::Identifier]
    );

    for (source, elements) in [
        ("()", 0),
        ("(a)", 1),
        ("(a,)", 1),
        ("(a,b,)", 2),
        ("(A\nB)", 2),
        ("(\n  A\n  B\n)", 2),
    ] {
        let (green, exit) = run_pattern(source);
        assert_eq!(green.to_string(), source, "{source:?}");
        assert!(matches!(exit, Err(Either::Right(_))), "{source:?}");
        let pattern = pattern_node(green);
        let parenthesized = pattern
            .children()
            .find(|node| node.kind() == SyntaxKind::ParenthesizedPattern)
            .expect("ParenthesizedPattern");
        assert_eq!(
            parenthesized
                .children()
                .filter(|node| node.kind() == SyntaxKind::Pattern)
                .count(),
            elements,
            "{source:?}"
        );
        assert!(
            !parenthesized
                .descendants()
                .any(|node| matches!(node.kind(), SyntaxKind::Missing | SyntaxKind::Error)),
            "{source:?}"
        );
    }
}

#[test]
fn standalone_patterns_keep_fixed_tail_order_and_colon_handoffs() {
    let (green, exit) = run_pattern("A as x | B as c");
    assert_eq!(green.to_string(), "A as x | B as c");
    assert!(matches!(exit, Err(Either::Right(_))));
    let pattern = pattern_node(green);
    assert_eq!(
        pattern
            .children()
            .map(|node| node.kind())
            .collect::<Vec<_>>(),
        [
            SyntaxKind::IdentifierPattern,
            SyntaxKind::PatternAliasTail,
            SyntaxKind::PatternAlternationTail,
        ]
    );
    let alternation = pattern
        .children()
        .find(|node| node.kind() == SyntaxKind::PatternAlternationTail)
        .expect("PatternAlternationTail");
    let rhs = alternation
        .children()
        .find(|node| node.kind() == SyntaxKind::Pattern)
        .expect("alternation RHS");
    assert!(
        rhs.children()
            .any(|node| node.kind() == SyntaxKind::PatternAliasTail)
    );

    let (green, exit) = run_pattern_with_colon_stop(":foo: body", true);
    assert_eq!(green.to_string(), ":foo");
    assert!(matches!(
        exit,
        Err(Either::Left(item))
            if matches!(item.payload, Payload::Token(ref token) if token.kind == TokenKind::Colon)
    ));

    let (green, exit) = run_pattern_with_colon_stop(": body", true);
    assert_eq!(green.to_string(), "");
    assert!(matches!(
        exit,
        Err(Either::Left(item))
            if matches!(item.payload, Payload::Token(ref token) if token.kind == TokenKind::Colon)
    ));
}

#[test]
fn standalone_patterns_keep_list_record_and_annotation_owners_local() {
    for (source, items, spreads) in [
        ("[]", 0, 0),
        ("[a]", 1, 0),
        ("[a,b,]", 2, 0),
        ("[a\nb]", 2, 0),
        ("[..head, tail]", 2, 1),
    ] {
        let (green, exit) = run_pattern(source);
        assert_eq!(green.to_string(), source, "{source:?}");
        assert!(matches!(exit, Err(Either::Right(_))), "{source:?}");
        let pattern = pattern_node(green);
        let list = pattern
            .children()
            .find(|node| node.kind() == SyntaxKind::ListPattern)
            .expect("ListPattern");
        assert_eq!(
            list.children()
                .filter(|node| {
                    matches!(
                        node.kind(),
                        SyntaxKind::Pattern | SyntaxKind::ListPatternSpreadItem
                    )
                })
                .count(),
            items,
            "{source:?}"
        );
        assert_eq!(
            list.children()
                .filter(|node| node.kind() == SyntaxKind::ListPatternSpreadItem)
                .count(),
            spreads,
            "{source:?}"
        );
        assert!(
            !list
                .descendants()
                .any(|node| matches!(node.kind(), SyntaxKind::Missing | SyntaxKind::Error)),
            "{source:?}"
        );
    }

    for (source, fields, spreads) in [
        ("{}", 0, 0),
        ("{a}", 1, 0),
        ("{a: b, c = 1}", 2, 0),
        ("{..head, width: local_width}", 1, 1),
    ] {
        let (green, exit) = run_pattern(source);
        assert_eq!(green.to_string(), source, "{source:?}");
        assert!(matches!(exit, Err(Either::Right(_))), "{source:?}");
        let pattern = pattern_node(green);
        let record = pattern
            .children()
            .find(|node| node.kind() == SyntaxKind::RecordPattern)
            .expect("RecordPattern");
        assert_eq!(
            record
                .children()
                .filter(|node| node.kind() == SyntaxKind::RecordPatternField)
                .count(),
            fields,
            "{source:?}"
        );
        assert_eq!(
            record
                .children()
                .filter(|node| node.kind() == SyntaxKind::RecordPatternSpreadItem)
                .count(),
            spreads,
            "{source:?}"
        );
        assert!(
            !record
                .descendants()
                .any(|node| matches!(node.kind(), SyntaxKind::Missing | SyntaxKind::Error)),
            "{source:?}"
        );
    }

    for source in ["x:Int", "A | B as c: Int", "{a: A: Inner}", "{a: A}: Outer"] {
        let (green, exit) = run_pattern(source);
        assert_eq!(green.to_string(), source, "{source:?}");
        assert!(matches!(exit, Err(Either::Right(_))), "{source:?}");
        let root = SyntaxNode::new_root(green);
        assert_eq!(
            root.descendants()
                .filter(|node| node.kind() == SyntaxKind::PatternTypeAnnotation)
                .count(),
            1,
            "{source:?}"
        );
        assert!(
            root.descendants()
                .any(|node| node.kind() == SyntaxKind::TypeExpression),
            "{source:?}"
        );
    }

    let (green, _) = run_pattern("A | B as c: Int");
    assert_eq!(
        pattern_node(green)
            .children()
            .map(|node| node.kind())
            .collect::<Vec<_>>(),
        [
            SyntaxKind::IdentifierPattern,
            SyntaxKind::PatternAlternationTail,
            SyntaxKind::PatternTypeAnnotation,
        ]
    );

    let (green, exit) = run_pattern("x: Int: Other");
    assert_eq!(green.to_string(), "x: Int");
    assert!(matches!(
        exit,
        Err(Either::Left(item))
            if matches!(item.payload, Payload::Token(ref token) if token.kind == TokenKind::Colon)
    ));

    let (green, exit) = run_pattern("x\n  : Int");
    assert_eq!(green.to_string(), "x\n  : Int");
    assert!(matches!(exit, Err(Either::Right(_))));
    assert!(
        SyntaxNode::new_root(green)
            .descendants()
            .any(|node| node.kind() == SyntaxKind::PatternTypeAnnotation)
    );

    let (green, exit) = run_pattern("x\n: Int");
    assert_eq!(green.to_string(), "x");
    assert!(matches!(
        exit,
        Err(Either::Left(item))
            if matches!(item.payload, Payload::Token(ref token) if token.kind == TokenKind::Colon)
                && item.leading.0.iter().any(|part| part.kind == TriviaKind::Newline)
    ));
}

#[test]
fn standalone_patterns_recover_primary_alias_and_alternation_slots_locally() {
    let (green, exit) = run_pattern("");
    assert!(matches!(exit, Err(Either::Right(_))));
    assert_eq!(
        pattern_node(green)
            .children()
            .filter(|node| node.kind() == SyntaxKind::Missing)
            .count(),
        1
    );

    let (green, exit) = run_pattern("@ x");
    assert_eq!(green.to_string(), "@ x");
    assert!(matches!(exit, Err(Either::Right(_))));
    let pattern = pattern_node(green);
    let errors = pattern
        .children()
        .filter(|node| node.kind() == SyntaxKind::Error)
        .collect::<Vec<_>>();
    assert_eq!(errors.len(), 1);
    assert_eq!(errors[0].text().to_string(), "@ ");
    assert!(
        pattern
            .children()
            .any(|node| node.kind() == SyntaxKind::IdentifierPattern)
    );
    assert_eq!(
        pattern
            .children()
            .filter(|node| node.kind() == SyntaxKind::Missing)
            .count(),
        0
    );

    let (green, exit) = run_pattern("A as");
    assert_eq!(green.to_string(), "A as");
    assert!(matches!(exit, Err(Either::Right(_))));
    let alias = pattern_node(green)
        .children()
        .find(|node| node.kind() == SyntaxKind::PatternAliasTail)
        .expect("PatternAliasTail");
    assert_eq!(
        alias
            .children()
            .filter(|node| node.kind() == SyntaxKind::Missing)
            .count(),
        1
    );

    let (green, exit) = run_pattern("A as $x");
    assert_eq!(green.to_string(), "A as $x");
    assert!(matches!(exit, Err(Either::Right(_))));
    let alias = pattern_node(green)
        .children()
        .find(|node| node.kind() == SyntaxKind::PatternAliasTail)
        .expect("PatternAliasTail");
    let errors = alias
        .children()
        .filter(|node| node.kind() == SyntaxKind::Error)
        .collect::<Vec<_>>();
    assert_eq!(errors.len(), 1);
    assert_eq!(errors[0].text().to_string(), "$x");
    assert_eq!(
        alias
            .children()
            .filter(|node| node.kind() == SyntaxKind::Missing)
            .count(),
        0
    );

    let (green, exit) = run_pattern("A |");
    assert_eq!(green.to_string(), "A |");
    assert!(matches!(exit, Err(Either::Right(_))));
    let alternation = pattern_node(green)
        .children()
        .find(|node| node.kind() == SyntaxKind::PatternAlternationTail)
        .expect("PatternAlternationTail");
    assert_eq!(
        alternation
            .descendants()
            .filter(|node| node.kind() == SyntaxKind::Missing)
            .count(),
        1
    );

    let (green, exit) = run_pattern("A | | B");
    assert_eq!(green.to_string(), "A | | B");
    assert!(matches!(exit, Err(Either::Right(_))));
    let alternation = pattern_node(green)
        .children()
        .find(|node| node.kind() == SyntaxKind::PatternAlternationTail)
        .expect("PatternAlternationTail");
    let rhs = alternation
        .children()
        .find(|node| node.kind() == SyntaxKind::Pattern)
        .expect("alternation RHS");
    assert_eq!(
        rhs.children()
            .filter(|node| node.kind() == SyntaxKind::Missing)
            .count(),
        1
    );
    assert_eq!(
        rhs.children()
            .filter(|node| node.kind() == SyntaxKind::PatternAlternationTail)
            .count(),
        1
    );

    let (green, exit) = run_pattern(":");
    assert_eq!(green.to_string(), ":");
    assert!(matches!(exit, Err(Either::Right(_))));
    let symbol = pattern_node(green)
        .children()
        .find(|node| node.kind() == SyntaxKind::SymbolPattern)
        .expect("SymbolPattern");
    assert_eq!(
        symbol
            .children()
            .filter(|node| node.kind() == SyntaxKind::Missing)
            .count(),
        1
    );

    for (source, tail) in [
        ("@ as x", SyntaxKind::PatternAliasTail),
        ("@ : T", SyntaxKind::PatternTypeAnnotation),
    ] {
        let (green, exit) = run_pattern(source);
        assert_eq!(green.to_string(), source, "{source:?}");
        assert!(matches!(exit, Err(Either::Right(_))), "{source:?}");
        let pattern = pattern_node(green);
        assert!(
            pattern.children().any(|node| node.kind() == tail),
            "{source:?}"
        );
    }

    let (green, exit) = run_pattern("A as @ ,");
    assert_eq!(green.to_string(), "A as @");
    let Err(Either::Left(item)) = exit else {
        panic!("comma handoff expected");
    };
    assert!(matches!(item.payload, Payload::Token(ref token) if token.kind == TokenKind::Comma));
    assert_eq!(
        item.leading
            .0
            .iter()
            .map(|trivia| &*trivia.text)
            .collect::<String>(),
        " "
    );
    let alias = pattern_node(green)
        .children()
        .find(|node| node.kind() == SyntaxKind::PatternAliasTail)
        .expect("PatternAliasTail");
    let errors = alias
        .children()
        .filter(|node| node.kind() == SyntaxKind::Error)
        .collect::<Vec<_>>();
    assert_eq!(errors.len(), 1);
    assert_eq!(errors[0].text().to_string(), "@");
    assert_eq!(
        alias
            .children()
            .filter(|node| node.kind() == SyntaxKind::Missing)
            .count(),
        0
    );
}

#[test]
fn standalone_pattern_recovery_leaves_caller_boundaries_and_their_gaps_intact() {
    for (source, kind, leading) in [
        ("@ ,", TokenKind::Comma, " "),
        ("@ ]", TokenKind::RBracket, " "),
        ("@ : T", TokenKind::Colon, " "),
        ("@\nT", TokenKind::Identifier, "\n"),
    ] {
        let colon_stop = kind == TokenKind::Colon;
        let (green, exit) = run_pattern_with_colon_stop(source, colon_stop);
        assert_eq!(green.to_string(), "@", "{source:?}");
        let Err(Either::Left(item)) = exit else {
            panic!("caller boundary expected: {source:?}");
        };
        assert!(
            matches!(item.payload, Payload::Token(ref token) if token.kind == kind),
            "{source:?}"
        );
        assert_eq!(
            item.leading
                .0
                .iter()
                .map(|trivia| &*trivia.text)
                .collect::<String>(),
            leading,
            "{source:?}"
        );
    }
}

#[test]
fn standalone_patterns_keep_parenthesized_and_list_recovery_inside_their_owners() {
    for (source, owner, patterns, expected_missing, expected_errors) in [
        ("(,a)", SyntaxKind::ParenthesizedPattern, 2, 1, 0),
        ("(a b)", SyntaxKind::ParenthesizedPattern, 2, 1, 0),
        ("(a]", SyntaxKind::ParenthesizedPattern, 1, 1, 1),
        ("[,a]", SyntaxKind::ListPattern, 2, 1, 0),
        ("[a b]", SyntaxKind::ListPattern, 2, 1, 0),
        ("[..]", SyntaxKind::ListPattern, 1, 1, 0),
        ("[..,a]", SyntaxKind::ListPattern, 2, 1, 0),
        ("[..@tail]", SyntaxKind::ListPattern, 1, 0, 1),
    ] {
        let (green, exit) = run_pattern(source);
        assert_eq!(green.to_string(), source, "{source:?}");
        assert!(matches!(exit, Err(Either::Right(_))), "{source:?}");
        let pattern = pattern_node(green);
        let delimited = pattern
            .children()
            .find(|node| node.kind() == owner)
            .expect("delimited Pattern owner");
        assert_eq!(
            delimited
                .descendants()
                .filter(|node| node.kind() == SyntaxKind::Pattern)
                .count(),
            patterns,
            "{source:?}"
        );
        assert_eq!(
            delimited
                .descendants()
                .filter(|node| node.kind() == SyntaxKind::Missing)
                .count(),
            expected_missing,
            "{source:?}"
        );
        let errors = delimited
            .descendants()
            .filter(|node| node.kind() == SyntaxKind::Error)
            .collect::<Vec<_>>();
        assert_eq!(errors.len(), expected_errors, "{source:?}");
        if source == "(a]" {
            assert_eq!(errors[0].text().to_string(), "]");
        }
        if source == "[..@tail]" {
            assert_eq!(errors[0].text().to_string(), "@");
        }
    }

    for (source, owner) in [
        ("(a\n", SyntaxKind::ParenthesizedPattern),
        ("[a\n", SyntaxKind::ListPattern),
    ] {
        let (green, exit) = run_pattern(source);
        assert_eq!(green.to_string(), source, "{source:?}");
        assert!(matches!(exit, Err(Either::Right(_))), "{source:?}");
        assert_eq!(trivia_parents(&green), [owner], "{source:?}");
    }
}

#[test]
fn standalone_patterns_keep_delimiter_and_malformed_list_item_recovery_local() {
    for (source, owner) in [
        ("(a", SyntaxKind::ParenthesizedPattern),
        ("[a", SyntaxKind::ListPattern),
    ] {
        let (green, exit) = run_pattern(source);
        assert_eq!(green.to_string(), source, "{source:?}");
        assert!(matches!(exit, Err(Either::Right(_))), "{source:?}");
        let delimited = pattern_node(green)
            .children()
            .find(|node| node.kind() == owner)
            .expect("delimited Pattern owner");
        assert_eq!(
            delimited
                .children()
                .filter(|node| node.kind() == SyntaxKind::Missing)
                .count(),
            1,
            "{source:?}"
        );
    }

    let (green, exit) = run_pattern("[a, @ b]");
    assert_eq!(green.to_string(), "[a, @ b]");
    assert!(matches!(exit, Err(Either::Right(_))));
    let list = pattern_node(green)
        .children()
        .find(|node| node.kind() == SyntaxKind::ListPattern)
        .expect("ListPattern");
    let items = list
        .children()
        .filter(|node| node.kind() == SyntaxKind::Pattern)
        .collect::<Vec<_>>();
    assert_eq!(items.len(), 2);
    let errors = items[1]
        .children()
        .filter(|node| node.kind() == SyntaxKind::Error)
        .collect::<Vec<_>>();
    assert_eq!(errors.len(), 1);
    assert_eq!(errors[0].text().to_string(), "@ ");
    assert!(
        items[1]
            .children()
            .any(|node| node.kind() == SyntaxKind::IdentifierPattern)
    );
    assert!(
        !items[1]
            .descendants()
            .any(|node| node.kind() == SyntaxKind::Missing)
    );

    let (green, exit) = run_pattern("[...,a]");
    assert_eq!(green.to_string(), "[...,a]");
    assert!(matches!(exit, Err(Either::Right(_))));
    let list = pattern_node(green)
        .children()
        .find(|node| node.kind() == SyntaxKind::ListPattern)
        .expect("ListPattern");
    let errors = list
        .descendants()
        .filter(|node| node.kind() == SyntaxKind::Error)
        .collect::<Vec<_>>();
    assert_eq!(errors.len(), 1);
    assert_eq!(errors[0].text().to_string(), "...");
    assert!(
        !list
            .descendants()
            .any(|node| node.kind() == SyntaxKind::ListPatternSpreadItem)
    );
    assert_eq!(
        list.children()
            .filter(|node| node.kind() == SyntaxKind::Pattern)
            .count(),
        2
    );
    assert_eq!(
        list.children_with_tokens()
            .filter_map(|element| element.into_token())
            .filter(|token| token.kind() == SyntaxKind::Comma)
            .count(),
        1
    );
}

#[test]
fn standalone_patterns_keep_inter_child_trivia_with_the_introducing_owner() {
    let (green, exit) = run_pattern("A | B");
    assert!(matches!(exit, Err(Either::Right(_))));
    assert_eq!(
        trivia_parents(&green),
        [SyntaxKind::Pattern, SyntaxKind::PatternAlternationTail]
    );

    let (green, exit) = run_pattern("(A\nB)");
    assert!(matches!(exit, Err(Either::Right(_))));
    assert_eq!(trivia_parents(&green), [SyntaxKind::ParenthesizedPattern]);

    let (green, exit) = run_pattern("{a: b, c = 1}");
    assert!(matches!(exit, Err(Either::Right(_))));
    assert_eq!(
        trivia_parents(&green),
        [
            SyntaxKind::RecordPatternField,
            SyntaxKind::RecordPattern,
            SyntaxKind::RecordPatternField,
            SyntaxKind::RecordPatternField,
        ]
    );

    let (green, exit) = run_pattern("x : T");
    assert!(matches!(exit, Err(Either::Right(_))));
    assert_eq!(
        trivia_parents(&green),
        [SyntaxKind::Pattern, SyntaxKind::PatternTypeAnnotation]
    );

    for source in ["A |\n  B\n  : T", "A |\n  B\n    : T"] {
        let (green, exit) = run_pattern(source);
        assert_eq!(green.to_string(), source, "{source:?}");
        assert!(matches!(exit, Err(Either::Right(_))), "{source:?}");
        let pattern = pattern_node(green);
        let alternation = pattern
            .children()
            .find(|node| node.kind() == SyntaxKind::PatternAlternationTail)
            .expect("PatternAlternationTail");
        let rhs = alternation
            .children()
            .find(|node| node.kind() == SyntaxKind::Pattern)
            .expect("alternation RHS");
        assert_eq!(
            rhs.children()
                .filter(|node| node.kind() == SyntaxKind::PatternTypeAnnotation)
                .count(),
            0,
            "{source:?}"
        );
        assert_eq!(
            pattern
                .children()
                .filter(|node| node.kind() == SyntaxKind::PatternTypeAnnotation)
                .count(),
            1,
            "{source:?}"
        );
    }

    for (source, annotations) in [("(A,\n  B\n  : T)", 0), ("(A,\n  B\n    : T)", 1)] {
        let (green, exit) = run_pattern(source);
        assert_eq!(green.to_string(), source, "{source:?}");
        assert!(matches!(exit, Err(Either::Right(_))), "{source:?}");
        assert_eq!(
            SyntaxNode::new_root(green)
                .descendants()
                .filter(|node| node.kind() == SyntaxKind::PatternTypeAnnotation)
                .count(),
            annotations,
            "{source:?}"
        );
    }
}

fn trivia_parents(green: &GreenNode) -> Vec<SyntaxKind> {
    SyntaxNode::new_root(green.clone())
        .descendants_with_tokens()
        .filter_map(|element| element.into_token())
        .filter(|token| matches!(token.kind(), SyntaxKind::Whitespace | SyntaxKind::Newline))
        .map(|token| token.parent().expect("trivia parent").kind())
        .collect()
}
