use super::*;

#[test]
fn dynamic_operator_roles_append_to_the_active_flat_chain() {
    let operators = dynamic_operator_table();
    let source = "~a + b++";
    let (green, exit) = run_with(source, &operators);
    assert_eq!(green.to_string(), source);
    assert!(matches!(exit, Some(Err(Either::Right(_)))));

    let root = SyntaxNode::new_root(green);
    let chain = root
        .children()
        .find(|node| node.kind() == SyntaxKind::OperatorChain)
        .expect("outer operator chain");
    assert_eq!(
        chain.children().map(|node| node.kind()).collect::<Vec<_>>(),
        [
            SyntaxKind::PrefixOperatorUse,
            SyntaxKind::IdentifierExpression,
            SyntaxKind::InfixOperatorUse,
            SyntaxKind::IdentifierExpression,
            SyntaxKind::SuffixOperatorUse,
        ]
    );
    assert_eq!(
        root.descendants_with_tokens()
            .filter_map(|element| element.into_token())
            .map(|token| (token.kind(), token.text().to_owned()))
            .collect::<Vec<_>>(),
        [
            (SyntaxKind::Operator, "~".to_owned()),
            (SyntaxKind::Identifier, "a".to_owned()),
            (SyntaxKind::Whitespace, " ".to_owned()),
            (SyntaxKind::Operator, "+".to_owned()),
            (SyntaxKind::Whitespace, " ".to_owned()),
            (SyntaxKind::Identifier, "b".to_owned()),
            (SyntaxKind::Operator, "++".to_owned()),
        ]
    );

    let (green, exit) = run_with("?", &operators);
    assert!(matches!(exit, Some(Err(Either::Right(_)))));
    assert!(
        SyntaxNode::new_root(green)
            .descendants()
            .any(|node| node.kind() == SyntaxKind::NullfixOperatorUse)
    );
}

#[test]
fn dynamic_operator_candidate_fallback_is_site_aware() {
    let operators = OperatorTable::from_declarations([
        OperatorDeclaration::new(
            "+!",
            OperatorFixities::new()
                .with_infix(BindingPower::scalar(50), BindingPower::new(50, [1])),
        ),
        OperatorDeclaration::new(
            "+",
            OperatorFixities::new().with_prefix(BindingPower::scalar(70)),
        ),
        OperatorDeclaration::new(
            "!",
            OperatorFixities::new()
                .with_prefix(BindingPower::scalar(80))
                .with_nullfix(),
        ),
    ])
    .expect("overlapping direct rewrite operator declarations");

    let (green, exit) = run_with("+!a", &operators);
    assert_eq!(green.to_string(), "+!a");
    assert!(matches!(exit, Some(Err(Either::Right(_)))));
    assert_eq!(
        operator_chain_children(&green),
        [
            SyntaxKind::PrefixOperatorUse,
            SyntaxKind::PrefixOperatorUse,
            SyntaxKind::IdentifierExpression,
        ]
    );

    let (green, exit) = run_with("a+!b", &operators);
    assert_eq!(green.to_string(), "a+!b");
    assert!(matches!(exit, Some(Err(Either::Right(_)))));
    assert_eq!(
        operator_chain_children(&green),
        [
            SyntaxKind::IdentifierExpression,
            SyntaxKind::InfixOperatorUse,
            SyntaxKind::IdentifierExpression,
        ]
    );
}

#[test]
fn dynamic_operator_raw_successor_probe_covers_value_starts_and_trivia() {
    let operators = OperatorTable::from_declarations([
        OperatorDeclaration::new(
            "?",
            OperatorFixities::new().with_prefix(BindingPower::scalar(70)),
        ),
        OperatorDeclaration::new("?", OperatorFixities::new().with_nullfix()),
        OperatorDeclaration::new(
            "!",
            OperatorFixities::new().with_prefix(BindingPower::scalar(80)),
        ),
        OperatorDeclaration::new("!", OperatorFixities::new().with_nullfix()),
    ])
    .expect("value-start operator declarations");

    for source in [
        "? \"",
        "? (",
        "? [",
        "? {",
        "? $",
        "? \\",
        "? %",
        "? _",
        "? '",
        "? α",
        "? 1",
        "? .",
        "? !",
        "? // line\n  α",
        "? /* outer /* inner */ outer */ α",
        "? \r\n  α",
    ] {
        let (use_, remaining) = scan_dynamic_operator(source, &operators, OperatorSite::Nud);
        assert!(
            matches!(use_, Some(OperatorUse::Prefix(_))),
            "{source:?} must select Prefix from raw successor evidence"
        );
        assert_eq!(remaining, source.strip_prefix('?').unwrap());
    }

    for source in ["? ", "? /* unterminated"] {
        let (use_, remaining) = scan_dynamic_operator(source, &operators, OperatorSite::Nud);
        assert_eq!(use_, Some(OperatorUse::Nullfix), "{source:?}");
        assert_eq!(remaining, source.strip_prefix('?').unwrap());
    }
}

#[test]
fn dynamic_operator_raw_rejection_keeps_outer_input_and_builder_unchanged() {
    let operators = OperatorTable::from_declarations([
        OperatorDeclaration::new(
            "?",
            OperatorFixities::new().with_prefix(BindingPower::scalar(70)),
        ),
        OperatorDeclaration::new("?", OperatorFixities::new().with_nullfix()),
    ])
    .expect("call-sensitive operator declaration");
    let mut input = "?(a)";
    let start = input.as_ptr();
    let mut recover = Recover::new(&operators);
    let mut builder = GreenNodeBuilder::new();
    builder.start_node(SyntaxKind::Root.into());
    let scanned = {
        let mut outer: RewriteIn = In::new(&mut input, &mut recover, &mut builder);
        outer.token(|lex| scan_operator(lex, OperatorSite::Nud, false, 0, 0))
    };
    assert!(scanned.is_none());
    assert_eq!(input.as_ptr(), start);
    assert_eq!(input, "?(a)");
    assert!(std::ptr::eq(recover.operators(), &operators));
    builder.finish_node();
    assert_eq!(builder.finish().to_string(), "");
}

#[test]
fn dynamic_operator_multibyte_boundary_falls_back_to_the_shorter_spelling() {
    let operators = OperatorTable::from_declarations([
        OperatorDeclaration::new(
            "!α",
            OperatorFixities::new()
                .with_infix(BindingPower::scalar(40), BindingPower::new(40, [1])),
        ),
        OperatorDeclaration::new(
            "!",
            OperatorFixities::new().with_prefix(BindingPower::scalar(70)),
        ),
    ])
    .expect("overlapping multibyte operator declarations");

    let (use_, remaining) = scan_dynamic_operator("!αx", &operators, OperatorSite::Nud);
    assert!(matches!(use_, Some(OperatorUse::Prefix(_))));
    assert_eq!(remaining, "αx");
}

#[test]
fn dynamic_operator_no_value_selects_the_without_value_fixity() {
    let operators = OperatorTable::from_declarations([OperatorDeclaration::new(
        "@",
        OperatorFixities::new()
            .with_infix(BindingPower::scalar(40), BindingPower::scalar(40))
            .with_suffix(BindingPower::scalar(70)),
    )])
    .expect("infix-suffix operator declaration");

    let (use_, remaining) = scan_dynamic_operator("@#", &operators, OperatorSite::Led);
    assert!(matches!(use_, Some(OperatorUse::Suffix(_))));
    assert_eq!(remaining, "#");

    let (use_, remaining) = scan_dynamic_operator("@b", &operators, OperatorSite::Led);
    assert!(matches!(use_, Some(OperatorUse::Infix { .. })));
    assert_eq!(remaining, "b");
}

#[test]
fn dynamic_operator_prefix_nullfix_and_call_colon_controls_stay_lexical() {
    let call_sensitive = OperatorTable::from_declarations([
        OperatorDeclaration::new(
            "?",
            OperatorFixities::new().with_prefix(BindingPower::scalar(70)),
        ),
        OperatorDeclaration::new("?", OperatorFixities::new().with_nullfix()),
    ])
    .expect("one call-sensitive operator declaration");

    let (green, exit) = run_with("? a", &call_sensitive);
    assert_eq!(green.to_string(), "? a");
    assert!(matches!(exit, Some(Err(Either::Right(_)))));
    assert!(
        SyntaxNode::new_root(green)
            .descendants()
            .any(|node| node.kind() == SyntaxKind::PrefixOperatorUse)
    );

    for source in ["?(a)", "?:a"] {
        let (green, exit) = run_with(source, &call_sensitive);
        assert_eq!(green.to_string(), "");
        assert_eq!(exit, None);
    }

    let mixed = OperatorTable::from_declarations([OperatorDeclaration::new(
        "?",
        OperatorFixities::new()
            .with_prefix(BindingPower::scalar(70))
            .with_infix(BindingPower::scalar(40), BindingPower::new(40, [1]))
            .with_nullfix(),
    )])
    .expect("mixed-fixity operator declaration");
    let (green, exit) = run_with("?(a)", &mixed);
    assert_eq!(green.to_string(), "?(a)");
    assert!(matches!(exit, Some(Err(Either::Right(_)))));
    assert!(
        SyntaxNode::new_root(green)
            .descendants()
            .any(|node| node.kind() == SyntaxKind::PrefixOperatorUse)
    );
}

#[test]
fn dynamic_operator_uses_delimited_baseline_and_matching_stop() {
    let infix = OperatorTable::from_declarations([OperatorDeclaration::new(
        "+",
        OperatorFixities::new().with_infix(BindingPower::scalar(40), BindingPower::new(40, [1])),
    )])
    .expect("one infix operator declaration");
    let (green, exit) = run_with("(\n  a +\n    b)", &infix);
    assert_eq!(green.to_string(), "(\n  a +\n    b)");
    assert!(matches!(exit, Some(Err(Either::Right(_)))));

    let (green, exit) = run_with("(a +\nb)", &infix);
    assert_eq!(green.to_string(), "(a");
    assert!(matches!(exit, Some(Err(Either::Left(_)))));

    let suffix_or_nullfix = OperatorTable::from_declarations([OperatorDeclaration::new(
        "~",
        OperatorFixities::new()
            .with_suffix(BindingPower::scalar(70))
            .with_nullfix(),
    )])
    .expect("one suffix-nullfix operator declaration");
    let (green, exit) = run_with("(a~)", &suffix_or_nullfix);
    assert_eq!(green.to_string(), "(a~)");
    assert!(matches!(exit, Some(Err(Either::Right(_)))));
    assert!(
        SyntaxNode::new_root(green)
            .descendants()
            .any(|node| node.kind() == SyntaxKind::SuffixOperatorUse)
    );
}

#[test]
fn dynamic_operator_honours_every_delimited_active_stop() {
    let suffix_or_nullfix = OperatorTable::from_declarations([OperatorDeclaration::new(
        "~",
        OperatorFixities::new()
            .with_suffix(BindingPower::scalar(70))
            .with_nullfix(),
    )])
    .expect("suffix-nullfix operator declaration");

    for source in ["(a~,b)", "(a~;b)", "a[b~]", "a.{a~}"] {
        let (green, exit) = run_with(source, &suffix_or_nullfix);
        assert_eq!(green.to_string(), source, "{source:?}");
        assert!(matches!(exit, Some(Err(Either::Right(_)))), "{source:?}");
        assert!(
            SyntaxNode::new_root(green)
                .descendants()
                .any(|node| node.kind() == SyntaxKind::SuffixOperatorUse),
            "{source:?} must select the suffix at its active stop"
        );
    }
}

#[test]
fn dynamic_operator_lower_bp_handoff_preserves_trivia_and_flat_output() {
    let outer = OperatorDeclaration::new(
        "+",
        OperatorFixities::new().with_infix(BindingPower::scalar(10), BindingPower::scalar(50)),
    );
    let lower = OperatorDeclaration::new(
        "*",
        OperatorFixities::new().with_infix(BindingPower::scalar(20), BindingPower::scalar(20)),
    );
    let higher = OperatorDeclaration::new(
        "*",
        OperatorFixities::new().with_infix(BindingPower::scalar(60), BindingPower::scalar(60)),
    );
    let source = "a + b /* carry */ * c";

    let handoff = OperatorTable::from_declarations([outer.clone(), lower])
        .expect("lower binding-power table");
    let accepted =
        OperatorTable::from_declarations([outer, higher]).expect("higher binding-power table");
    let (handoff_green, handoff_exit) = run_with(source, &handoff);
    let (accepted_green, accepted_exit) = run_with(source, &accepted);

    assert_eq!(handoff_green.to_string(), source);
    assert_eq!(accepted_green.to_string(), source);
    assert!(matches!(handoff_exit, Some(Err(Either::Right(_)))));
    assert!(matches!(accepted_exit, Some(Err(Either::Right(_)))));
    assert_eq!(
        operator_chain_children(&handoff_green),
        [
            SyntaxKind::IdentifierExpression,
            SyntaxKind::InfixOperatorUse,
            SyntaxKind::IdentifierExpression,
            SyntaxKind::InfixOperatorUse,
            SyntaxKind::IdentifierExpression,
        ]
    );
    assert_eq!(
        operator_chain_children(&handoff_green),
        operator_chain_children(&accepted_green),
        "only binding powers differ; flat CST stays fixed"
    );
    assert!(
        SyntaxNode::new_root(handoff_green)
            .descendants_with_tokens()
            .filter_map(|element| element.into_token())
            .any(|token| token.kind() == SyntaxKind::BlockComment && token.text() == "/* carry */")
    );
}
