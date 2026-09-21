use crate::lexical::yumark::{FenceOpener, FencePrefixPolicy};
use crate::structural_diagnostic::StructuralKind;
use crate::tests::support::*;

fn typed_binding<'a>(
    source: &'a str,
    origin: usize,
) -> (GreenNode, NormalizedExit, &'a str, Vec<StructuralFact>) {
    typed_binding_fenced(source, origin, None, 0)
}

fn typed_binding_fenced<'a>(
    source: &'a str,
    origin: usize,
    fence: Option<&FenceBoundary>,
    stops: Stops,
) -> (GreenNode, NormalizedExit, &'a str, Vec<StructuralFact>) {
    let operators = OperatorTable::empty();
    let mut input = source;
    let mut recover = Recover::new_for_test(&operators);
    let mut builder = GreenNodeBuilder::new();
    builder.start_node(SyntaxKind::Root.into());
    let exit = statement_normalized(
        crate::cursor::SyntaxIn::new(&mut input, &mut recover, &mut builder),
        0,
        stops,
        origin,
        LineEntry::InLine,
        fence,
        Some(crate::ambient_claim::AmbientClaimView::root_statement(0)).into(),
        Some(crate::sequence::SequenceOwner::RootStatement),
    );
    builder.finish_node();
    let green = finish_with_discarded_recoveries(builder, recover);
    let facts = structural_facts(&green);
    (green, exit, input, facts)
}

#[test]
fn binding_body_keeps_complete_protected_items_and_quoted_fences() {
    for (source, text, range, kind) in [
        ("my x =  ]tail", "my x =", 6..6, StructuralKind::Missing),
        (
            "my x = @  ]tail",
            "my x = @",
            7..8,
            StructuralKind::ErrorGroup,
        ),
    ] {
        let stops = crate::lexical::stops::stops_for(TokenKind::RBracket);
        let (green, exit, suffix, facts) = typed_binding_fenced(source, 100, None, stops);
        assert_eq!(green.to_string(), text);
        assert_eq!(suffix, "tail");
        assert_eq!(facts, [(kind, range)]);
        let NormalizedExit::Complete(Err(Either::Left(item)), _) = exit else {
            panic!("active close remains pending")
        };
        assert_eq!(token_kind(&item), Some(TokenKind::RBracket));
        assert_eq!(
            item.extent(100 + source.len() - suffix.len())
                .recovery_range()
                .start,
            100 + text.len()
        );
    }
    for (source, fact) in [
        ("my x =  ;tail", (StructuralKind::Missing, 6..6)),
        ("my x = @  ;tail", (StructuralKind::ErrorGroup, 7..8)),
        ("my x =\r\nnext tail", (StructuralKind::Missing, 6..6)),
        ("my x = @\r\nnext tail", (StructuralKind::ErrorGroup, 7..8)),
    ] {
        let (_, exit, suffix, facts) = typed_binding(source, 100);
        let NormalizedExit::Complete(Err(Either::Left(item)), _) = exit else {
            panic!("pending boundary: {source:?}")
        };
        let pending_end = 100 + source.len() - suffix.len();
        let protected_start = if source.contains('@') { 108 } else { 106 };
        assert_eq!(
            item.extent(pending_end).recovery_range().start,
            protected_start,
            "{source:?}"
        );
        assert_eq!(facts, [fact]);
    }
    let fence = FenceBoundary {
        opener: FenceOpener {
            line: 0,
            marker: 0..3,
            marker_width: 3,
        },
        prefix_policy: FencePrefixPolicy::ActivePrefixQuote { depth: 2, base: 0 },
        close_column: 0,
    };
    for (source, text, kind, range) in [
        ("my x =\r\n>> ```", "my x =", StructuralKind::Missing, 6..6),
        (
            "my x = @\r\n>> ```",
            "my x = @",
            StructuralKind::ErrorGroup,
            7..8,
        ),
    ] {
        let (green, exit, _, facts) = typed_binding_fenced(source, 100, Some(&fence), 0);
        assert_eq!(green.to_string(), text);
        assert_eq!(facts, [(kind, range)]);
        assert!(
            matches!(exit, NormalizedExit::Complete(Err(Either::Left(ref item)), _) if item.payload_view().is_boundary())
        );
        let (again, _, _, repeated_facts) = typed_binding_fenced(source, 100, Some(&fence), 0);
        assert_eq!(again, green);
        assert_eq!(repeated_facts, facts);
    }
}

#[test]
fn binding_initial_slots_publish_exact_structural_facts() {
    for (source, kind, range, text) in [
        ("my", StructuralKind::Missing, 2..2, "my"),
        ("my = value", StructuralKind::Missing, 3..3, "my = value"),
        (
            "my @ x = value",
            StructuralKind::ErrorGroup,
            3..4,
            "my @ x = value",
        ),
        (
            "my @ = value",
            StructuralKind::ErrorGroup,
            3..4,
            "my @ = value",
        ),
        ("my @ ;", StructuralKind::ErrorGroup, 3..4, "my @"),
        ("my x =  ", StructuralKind::Missing, 8..8, "my x =  "),
        ("my x =  ;", StructuralKind::Missing, 6..6, "my x ="),
        ("my x =\r\nnext", StructuralKind::Missing, 6..6, "my x ="),
        (
            "my x = @ @ value",
            StructuralKind::ErrorGroup,
            7..10,
            "my x = @ @ value",
        ),
        ("my x = @  ;", StructuralKind::ErrorGroup, 7..8, "my x = @"),
        (
            "my x = @\r\nnext",
            StructuralKind::ErrorGroup,
            7..8,
            "my x = @",
        ),
        ("my x = @  ", StructuralKind::ErrorGroup, 7..8, "my x = @  "),
        (
            "my 界 = @ λ",
            StructuralKind::ErrorGroup,
            9..10,
            "my 界 = @ λ",
        ),
    ] {
        for origin in [0, 4103] {
            let (green, _, _, facts) = typed_binding(source, origin);
            assert_eq!(green.to_string(), text, "{source:?}");
            assert_eq!(facts, [(kind, range.clone())], "{source:?}");
            let (again, _, _, repeated_facts) = typed_binding(source, origin);
            assert_eq!(again, green);
            assert_eq!(repeated_facts, facts);
        }
    }
}

#[test]
fn binding_admitted_children_keep_their_own_structural_facts() {
    for (source, fact) in [
        ("my (,) = value", (StructuralKind::Missing, 4..4)),
        ("my x: = value", (StructuralKind::Missing, 6..6)),
        ("my x = (", (StructuralKind::Missing, 8..8)),
    ] {
        let (_, _, _, facts) = typed_binding(source, 0);
        assert_eq!(facts, [fact], "{source:?}");
    }
}

fn binding(green: &GreenNode) -> SyntaxNode {
    SyntaxNode::new_root(green.clone())
        .descendants()
        .find(|node| node.kind() == SyntaxKind::BindingStatement)
        .expect("BindingStatement")
}

#[test]
fn public_parser_binding_header_uses_pattern_ml_application_and_hands_off_equals() {
    use std::sync::Arc;

    let source: Arc<crate::SourceText> = Arc::from("my f x = x");
    let header = Arc::new(crate::scan_header(Arc::clone(&source)));
    let parsed = crate::parse_file(source, header, Arc::new(crate::SyntaxEnvironment::empty()));
    assert!(parsed.syntax_diagnostics().unwrap().is_empty());
    assert!(parsed.structural_recoveries().is_empty());
    let declaration = binding(parsed.green());
    let header = declaration.first_child().expect("BindingHeader");
    let targets = header.children().collect::<Vec<_>>();
    let [target] = targets.as_slice() else {
        panic!("one Pattern target")
    };
    assert_eq!(target.kind(), SyntaxKind::Pattern);
    assert_eq!(
        target
            .children()
            .map(|node| node.kind())
            .collect::<Vec<_>>(),
        [
            SyntaxKind::IdentifierPattern,
            SyntaxKind::PatternMlApplicationTail,
        ]
    );
    let application = target.last_child().expect("PatternMlApplicationTail");
    assert_eq!(
        application
            .children()
            .map(|node| node.kind())
            .collect::<Vec<_>>(),
        [SyntaxKind::Pattern]
    );
    assert_eq!(
        application
            .first_child()
            .expect("argument Pattern")
            .children()
            .map(|node| node.kind())
            .collect::<Vec<_>>(),
        [SyntaxKind::IdentifierPattern]
    );
    let equals = header
        .children_with_tokens()
        .filter_map(|element| element.into_token())
        .filter(|token| token.kind() == SyntaxKind::Equals)
        .collect::<Vec<_>>();
    assert_eq!(equals.len(), 1);
    assert_eq!(usize::from(equals[0].text_range().start()), 7);
    assert_eq!(
        declaration.last_child().expect("BindingBody").to_string(),
        " x"
    );
}

#[test]
fn binding_annotation_equals_stays_outside_type_recovery() {
    for source in [
        "my x: = value",
        "my x: @ = value",
        "my x: A->@ = value",
        "my x: F(=T) = value",
    ] {
        let (green, _) = run_statement(source);
        assert_eq!(green.to_string(), source);
        let node = binding(&green);
        let header = node
            .children()
            .find(|child| child.kind() == SyntaxKind::BindingHeader)
            .unwrap();
        let equals = header
            .children_with_tokens()
            .filter_map(|element| element.into_token())
            .filter(|token| token.kind() == SyntaxKind::Equals)
            .collect::<Vec<_>>();
        assert_eq!(equals.len(), 1, "{source:?}\n{node:#?}");
        assert_eq!(
            usize::from(equals[0].text_range().start()),
            source.rfind('=').unwrap()
        );
        assert_eq!(
            node.children()
                .find(|child| child.kind() == SyntaxKind::BindingBody)
                .unwrap()
                .to_string(),
            " value"
        );
        let annotation = header
            .descendants()
            .find(|child| child.kind() == SyntaxKind::PatternTypeAnnotation)
            .unwrap();
        assert_eq!(
            annotation
                .descendants()
                .filter(|child| child.kind() == SyntaxKind::Missing)
                .count(),
            usize::from(source == "my x: = value")
        );
        assert_eq!(
            crate::tests::recovery_output::recovery_groups(&annotation)
                .into_iter()
                .count(),
            usize::from(source != "my x: = value")
        );
    }
}

#[test]
fn binding_c8_builds_canonical_header_and_optional_body_topology() {
    for (source, visibility) in [
        ("my x", SyntaxKind::MyKw),
        ("our x", SyntaxKind::OurKw),
        ("pub x", SyntaxKind::PubKw),
    ] {
        let (green, exit) = run_statement(source);
        assert_eq!(green.to_string(), source, "{source:?}");
        assert!(matches!(exit, Some(Err(Either::Right(_)))), "{source:?}");
        let declaration = binding(&green);
        assert_eq!(
            declaration
                .children()
                .map(|node| node.kind())
                .collect::<Vec<_>>(),
            [SyntaxKind::BindingHeader],
            "{source:?}"
        );
        let header = declaration.first_child().expect("BindingHeader");
        assert_eq!(
            header.first_token().map(|token| token.kind()),
            Some(visibility)
        );
        assert!(
            header
                .children()
                .any(|node| node.kind() == SyntaxKind::Pattern)
        );
        assert!(
            !declaration
                .children()
                .any(|node| node.kind() == SyntaxKind::BindingBody)
        );
    }

    let (green, exit) = run_statement("my A | B as name = value");
    assert_eq!(green.to_string(), "my A | B as name = value");
    assert!(matches!(exit, Some(Err(Either::Right(_)))));
    let declaration = binding(&green);
    assert_eq!(
        declaration
            .children()
            .map(|node| node.kind())
            .collect::<Vec<_>>(),
        [SyntaxKind::BindingHeader, SyntaxKind::BindingBody]
    );
    let header = declaration.first_child().expect("BindingHeader");
    assert_eq!(
        header
            .children_with_tokens()
            .filter_map(|element| element.into_token())
            .filter(|token| token.kind() == SyntaxKind::Equals)
            .count(),
        1
    );
    let body = declaration.last_child().expect("BindingBody");
    assert_eq!(
        body.children().map(|node| node.kind()).collect::<Vec<_>>(),
        [SyntaxKind::OperatorChain]
    );

    let source = "my /*after visibility*/ x /*before equals*/ = /*after equals*/ value";
    let (green, _) = run_statement(source);
    assert_eq!(green.to_string(), source);
    let declaration = binding(&green);
    let header = declaration.first_child().expect("BindingHeader");
    let body = declaration.last_child().expect("BindingBody");
    assert_eq!(
        header
            .children_with_tokens()
            .filter_map(|element| element.into_token())
            .filter(|token| token.kind() == SyntaxKind::BlockComment)
            .count(),
        2
    );
    assert_eq!(
        body.children_with_tokens()
            .filter_map(|element| element.into_token())
            .filter(|token| token.kind() == SyntaxKind::BlockComment)
            .count(),
        1
    );
    assert!(
        !header
            .descendants()
            .find(|node| node.kind() == SyntaxKind::Pattern)
            .expect("Pattern")
            .descendants_with_tokens()
            .filter_map(|element| element.into_token())
            .any(|token| token.kind() == SyntaxKind::BlockComment)
    );
}

#[test]
fn binding_c8_reuses_full_current_pattern_surface_and_exact_equals_stop() {
    for source in [
        "my (a, b) = value",
        "my [a, ..rest] = value",
        "my {a: b, c = 1} = value",
        "my :tag = value",
        "my x: T = value",
    ] {
        let (green, exit) = run_statement(source);
        assert_eq!(green.to_string(), source, "{source:?}");
        assert!(matches!(exit, Some(Err(Either::Right(_)))), "{source:?}");
        let declaration = binding(&green);
        assert_eq!(
            declaration
                .descendants_with_tokens()
                .filter_map(|element| element.into_token())
                .filter(|token| token.kind() == SyntaxKind::Equals)
                .count(),
            source.matches('=').count(),
            "{source:?}"
        );
        assert!(
            declaration
                .children()
                .any(|node| node.kind() == SyntaxKind::BindingBody)
        );
    }

    for source in ["my x == value", "my x => value"] {
        let (green, exit) = run_statement(source);
        assert_eq!(green.to_string(), "my x", "{source:?}");
        assert!(matches!(exit, Some(Err(Either::Left(_)))), "{source:?}");
        assert!(
            !binding(&green)
                .children()
                .any(|node| node.kind() == SyntaxKind::BindingBody)
        );
    }

    let (green, exit) = run_statement("my x\n= y");
    assert_eq!(green.to_string(), "my x");
    assert!(matches!(
        exit,
        Some(Err(Either::Left(item)))
            if item.payload_view().token_kind() == Some(TokenKind::Equals)
                && item.leading_view().has_ordinary_newline()
    ));
    let declaration = binding(&green);
    assert!(
        !declaration
            .children()
            .any(|node| node.kind() == SyntaxKind::BindingBody)
    );
    assert!(
        !declaration
            .descendants_with_tokens()
            .filter_map(|element| element.into_token())
            .any(|token| token.kind() == SyntaxKind::Equals)
    );

    let source = "my x\n  = y";
    let (green, exit) = run_statement(source);
    assert_eq!(green.to_string(), source);
    assert!(matches!(exit, Some(Err(Either::Right(_)))));
    let declaration = binding(&green);
    assert!(
        declaration
            .children()
            .any(|node| node.kind() == SyntaxKind::BindingBody)
    );
    assert!(
        declaration
            .first_child()
            .expect("BindingHeader")
            .children_with_tokens()
            .filter_map(|element| element.into_token())
            .any(|token| token.kind() == SyntaxKind::Equals)
    );
}

#[test]
fn binding_c8_distinguishes_inline_strict_deeper_and_wrong_indent_bodies() {
    let (green, _) = run_statement("my x =  value");
    let body = binding(&green).last_child().expect("inline BindingBody");
    assert_eq!(body.text().to_string(), "  value");
    assert_eq!(
        body.children().map(|node| node.kind()).collect::<Vec<_>>(),
        [SyntaxKind::OperatorChain]
    );

    let source = "my x =\n  my y = 1\n  y";
    let (green, exit) = run_statement(source);
    assert_eq!(green.to_string(), source);
    assert!(matches!(exit, Some(Err(Either::Right(_)))));
    let body = binding(&green).last_child().expect("indented BindingBody");
    let block = body
        .children()
        .find(|node| node.kind() == SyntaxKind::IndentedStatementBlock)
        .expect("IndentedStatementBlock");
    assert_eq!(
        block
            .children()
            .filter(|node| node.kind() == SyntaxKind::Statement)
            .count(),
        2
    );
    assert_eq!(
        block
            .descendants()
            .filter(|node| node.kind() == SyntaxKind::BindingStatement)
            .count(),
        1
    );

    let (green, exit) = run_statement("my x =\ny");
    assert_eq!(green.to_string(), "my x =");
    assert!(matches!(exit, Some(Err(Either::Left(_)))));
    let body = binding(&green).last_child().expect("missing BindingBody");
    assert_eq!(
        body.children().map(|node| node.kind()).collect::<Vec<_>>(),
        [SyntaxKind::Missing]
    );
}

#[test]
fn binding_c8_totalizes_target_and_accepted_body_slots_once() {
    for (source, missing, error) in [
        ("my", 1, 0),
        ("my = value", 1, 0),
        ("my @ x = value", 0, 1),
        ("my x =", 1, 0),
        ("my x = @ value", 0, 1),
        ("my x = @", 0, 1),
    ] {
        let (green, exit) = run_statement(source);
        assert_eq!(green.to_string(), source, "{source:?}");
        assert!(matches!(exit, Some(Err(Either::Right(_)))), "{source:?}");
        let declaration = binding(&green);
        assert_eq!(
            declaration
                .descendants()
                .filter(|node| node.kind() == SyntaxKind::Missing)
                .count(),
            missing,
            "{source:?}"
        );
        assert_eq!(
            crate::tests::recovery_output::recovery_groups(&declaration)
                .into_iter()
                .count(),
            error,
            "{source:?}"
        );
    }

    let (green, _) = run_statement("my x");
    assert!(
        !binding(&green)
            .descendants()
            .any(|node| node.kind() == SyntaxKind::Missing)
    );

    for (source, missing, error) in [("my x;", 0, 0), ("my x =;", 1, 0), ("my x = @;", 0, 1)] {
        let (green, exit) = run_statement(source);
        assert_eq!(
            green.to_string(),
            source.trim_end_matches(';'),
            "{source:?}"
        );
        assert!(matches!(
            exit,
            Some(Err(Either::Left(item)))
                if item.payload_view().token_kind() == Some(TokenKind::Semicolon)
        ));
        let declaration = binding(&green);
        assert_eq!(
            declaration
                .descendants()
                .filter(|node| node.kind() == SyntaxKind::Missing)
                .count(),
            missing,
            "{source:?}"
        );
        assert_eq!(
            crate::tests::recovery_output::recovery_groups(&declaration)
                .into_iter()
                .count(),
            error,
            "{source:?}"
        );
    }

    let (green, exit) = run_statement("my\nx");
    assert_eq!(green.to_string(), "my");
    assert!(matches!(
        exit,
        Some(Err(Either::Left(item)))
            if item.leading_view().has_ordinary_newline()
    ));
    assert_eq!(
        binding(&green)
            .descendants()
            .filter(|node| node.kind() == SyntaxKind::Missing)
            .count(),
        1
    );
}

#[test]
fn binding_body_inline_raw_slot_has_direct_missing_error_retry_and_boundary() {
    let direct = |node: &SyntaxNode| {
        node.children_with_tokens()
            .map(|element| {
                (
                    element.kind(),
                    usize::from(element.text_range().start())
                        ..usize::from(element.text_range().end()),
                )
            })
            .collect::<Vec<_>>()
    };
    let assert_no_invalid = |node: &SyntaxNode| {
        assert!(
            node.descendants()
                .all(|child| child.kind() != SyntaxKind::Invalid),
            "{node:#?}"
        );
    };
    let assert_binding_context = |declaration: &SyntaxNode| {
        assert_eq!(
            declaration
                .children()
                .map(|node| node.kind())
                .collect::<Vec<_>>(),
            [SyntaxKind::BindingHeader, SyntaxKind::BindingBody]
        );
        let header = declaration.children().next().unwrap();
        assert_eq!(header.kind(), SyntaxKind::BindingHeader);
        assert_eq!(
            header
                .children_with_tokens()
                .filter_map(|element| element.into_token())
                .filter(|token| token.kind() == SyntaxKind::Equals)
                .map(|token| {
                    usize::from(token.text_range().start())..usize::from(token.text_range().end())
                })
                .collect::<Vec<_>>(),
            [5..6]
        );
    };

    let (green, exit) = run_statement("my x =");
    assert_eq!(green.to_string(), "my x =");
    assert!(matches!(exit, Some(Err(Either::Right(_)))));
    let declaration = binding(&green);
    assert_binding_context(&declaration);
    let body = declaration
        .children()
        .find(|node| node.kind() == SyntaxKind::BindingBody)
        .unwrap();
    assert_eq!(direct(&body), [(SyntaxKind::Missing, 6..6)]);
    let missing = body.children().next().unwrap();
    assert_eq!(missing.kind(), SyntaxKind::Missing);
    assert_eq!(missing.parent(), Some(body.clone()));
    assert_no_invalid(&declaration);

    let (green, exit) = run_statement("my x = @ value");
    assert_eq!(green.to_string(), "my x = @ value");
    assert!(matches!(exit, Some(Err(Either::Right(_)))));
    let declaration = binding(&green);
    assert_binding_context(&declaration);
    let body = declaration
        .children()
        .find(|node| node.kind() == SyntaxKind::BindingBody)
        .unwrap();
    assert_eq!(
        direct(&body),
        [
            (SyntaxKind::Whitespace, 6..7),
            (SyntaxKind::Error, 7..8),
            (SyntaxKind::Whitespace, 8..9),
            (SyntaxKind::OperatorChain, 9..14),
        ]
    );
    let errors = body
        .children_with_tokens()
        .filter_map(|element| element.into_token())
        .filter(|token| token.kind() == SyntaxKind::Error)
        .collect::<Vec<_>>();
    assert_eq!(errors.len(), 1);
    assert_eq!(errors[0].parent(), Some(body.clone()));
    assert_eq!(
        errors[0].text_range(),
        rowan::TextRange::new(7.into(), 8.into())
    );
    let retry = body
        .children()
        .find(|node| node.kind() == SyntaxKind::OperatorChain)
        .unwrap();
    assert_eq!(retry.parent(), Some(body.clone()));
    assert_eq!(
        retry.children().map(|node| node.kind()).collect::<Vec<_>>(),
        [SyntaxKind::IdentifierExpression]
    );
    assert!(
        retry
            .descendants_with_tokens()
            .all(|element| element.kind() != SyntaxKind::Error)
    );
    assert_no_invalid(&declaration);

    let (green, exit) = run_statement("my x = @;");
    assert_eq!(green.to_string(), "my x = @");
    assert!(matches!(
        exit,
        Some(Err(Either::Left(item)))
            if item.payload_view().token_kind() == Some(TokenKind::Semicolon)
    ));
    let declaration = binding(&green);
    assert_binding_context(&declaration);
    let body = declaration
        .children()
        .find(|node| node.kind() == SyntaxKind::BindingBody)
        .unwrap();
    assert_eq!(
        direct(&body),
        [(SyntaxKind::Whitespace, 6..7), (SyntaxKind::Error, 7..8),]
    );
    let errors = body
        .children_with_tokens()
        .filter_map(|element| element.into_token())
        .filter(|token| token.kind() == SyntaxKind::Error)
        .collect::<Vec<_>>();
    assert_eq!(errors.len(), 1);
    assert_eq!(errors[0].parent(), Some(body.clone()));
    assert!(
        body.descendants()
            .all(|node| node.kind() != SyntaxKind::Missing)
    );
    assert_no_invalid(&declaration);

    let (green, exit) = run_statement("my x = @  ");
    assert_eq!(green.to_string(), "my x = @  ");
    assert!(matches!(exit, Some(Err(Either::Right(_)))));
    let declaration = binding(&green);
    assert_binding_context(&declaration);
    let body = declaration
        .children()
        .find(|node| node.kind() == SyntaxKind::BindingBody)
        .unwrap();
    assert_eq!(
        direct(&body),
        [
            (SyntaxKind::Whitespace, 6..7),
            (SyntaxKind::Error, 7..8),
            (SyntaxKind::Whitespace, 8..10),
        ]
    );
    let errors = body
        .children_with_tokens()
        .filter_map(|element| element.into_token())
        .filter(|token| token.kind() == SyntaxKind::Error)
        .collect::<Vec<_>>();
    assert_eq!(errors.len(), 1);
    assert_eq!(errors[0].parent(), Some(body.clone()));
    assert_eq!(
        errors[0].text_range(),
        rowan::TextRange::new(7.into(), 8.into())
    );
    assert!(
        body.descendants()
            .all(|node| node.kind() != SyntaxKind::Missing)
    );
    assert_no_invalid(&declaration);
}

#[test]
fn binding_c8_keeps_statement_head_reservation_source_only_and_exact() {
    let (green, _) = run_statement("my use = value");
    assert!(
        SyntaxNode::new_root(green)
            .descendants()
            .any(|node| node.kind() == SyntaxKind::BindingStatement)
    );

    for source in [
        "my use path",
        "my mod = value",
        "my struct = value",
        "my type = value",
        "my role = value",
        "my impl = value",
        "my cast = value",
        "my enum Name = value",
        "my error Name = value",
        "my act Name = value",
        "our enum = value",
        "pub act = value",
        "my lazy value",
        "my prefix value",
    ] {
        let (green, _) = run_statement(source);
        assert!(
            !SyntaxNode::new_root(green)
                .descendants()
                .any(|node| node.kind() == SyntaxKind::BindingStatement),
            "{source:?}"
        );
    }

    for source in [
        "my enum = value",
        "my error = value",
        "my act = value",
        "my lazy = value",
        "my prefix = value",
        "my infix = value",
        "my suffix = value",
        "my nullfix = value",
    ] {
        let (green, _) = run_statement(source);
        assert!(
            SyntaxNode::new_root(green)
                .descendants()
                .any(|node| node.kind() == SyntaxKind::BindingStatement),
            "{source:?}"
        );
    }

    for source in ["myx = value", "ours = value", "public = value"] {
        let (green, _) = run_statement(source);
        assert!(
            !SyntaxNode::new_root(green)
                .descendants()
                .any(|node| node.kind() == SyntaxKind::BindingStatement),
            "{source:?}"
        );
    }

    let operators = OperatorTable::from_declarations([OperatorDeclaration::new(
        "my",
        OperatorFixities::new().with_prefix(BindingPower::scalar(40)),
    )])
    .expect("visibility/operator collision table");
    let (green, _) = run_statement_with("my x = value", &operators);
    assert!(
        SyntaxNode::new_root(green)
            .descendants()
            .any(|node| node.kind() == SyntaxKind::BindingStatement)
    );
    let (green, _) = run_with("my x", &operators);
    let root = SyntaxNode::new_root(green);
    assert!(
        root.descendants()
            .any(|node| node.kind() == SyntaxKind::PrefixOperatorUse)
    );
    assert!(
        !root
            .descendants()
            .any(|node| node.kind() == SyntaxKind::BindingStatement)
    );
}

#[test]
fn binding_c8_is_canonical_in_braced_indented_and_with_statement_slots_only() {
    for source in [
        "{my x = 1; x}",
        "f:\n  my x = 1\n  x",
        "if c:\n  my x = 1\n  x",
        "case x:\n  p ->\n    my y = 1\n    y",
        "value with: my x = 1",
        "value with:\n  my x = 1\n  x",
    ] {
        let (green, exit) = run(source);
        assert_eq!(green.to_string(), source, "{source:?}");
        assert!(matches!(exit, Some(Err(Either::Right(_)))), "{source:?}");
        assert!(
            SyntaxNode::new_root(green)
                .descendants()
                .any(|node| node.kind() == SyntaxKind::BindingStatement),
            "{source:?}"
        );
    }

    for source in [
        "f: my x = 1",
        "if c: my x = 1",
        "case x: p -> my y = 1",
        "catch x: p -> my y = 1",
    ] {
        let (green, _) = run(source);
        assert!(
            !SyntaxNode::new_root(green)
                .descendants()
                .any(|node| node.kind() == SyntaxKind::BindingStatement),
            "{source:?}"
        );
    }
}

#[test]
fn binding_c8_leaves_statement_boundaries_and_opening_trivia_with_their_owners() {
    let source = "{my x = 1;  my y = 2}";
    let (green, exit) = run(source);
    assert_eq!(green.to_string(), source);
    assert!(matches!(exit, Some(Err(Either::Right(_)))));
    let root = SyntaxNode::new_root(green);
    let bindings = root
        .descendants()
        .filter(|node| node.kind() == SyntaxKind::BindingStatement)
        .collect::<Vec<_>>();
    assert_eq!(bindings.len(), 2);
    assert!(bindings.iter().all(|binding| {
        !binding
            .descendants_with_tokens()
            .filter_map(|element| element.into_token())
            .any(|token| token.kind() == SyntaxKind::Semicolon)
    }));
    let separator = root
        .descendants()
        .find(|node| node.kind() == SyntaxKind::BlockStatementSeparator)
        .expect("BlockStatementSeparator");
    assert_eq!(separator.text().to_string(), ";  ");

    let (green, exit) = run("f:\n  my x = 1\ny");
    assert_eq!(green.to_string(), "f:\n  my x = 1");
    assert!(matches!(exit, Some(Err(Either::Left(_)))));

    let source = "f:\n  my x =\n  y";
    let (green, exit) = run(source);
    assert_eq!(green.to_string(), source);
    assert!(matches!(exit, Some(Err(Either::Right(_)))));
    let root = SyntaxNode::new_root(green);
    let block = root
        .descendants()
        .find(|node| node.kind() == SyntaxKind::IndentedStatementBlock)
        .expect("IndentedStatementBlock");
    assert_eq!(
        block
            .children()
            .filter(|node| node.kind() == SyntaxKind::Statement)
            .count(),
        2
    );
    let binding = block
        .descendants()
        .find(|node| node.kind() == SyntaxKind::BindingStatement)
        .expect("BindingStatement");
    assert_eq!(
        binding
            .descendants()
            .filter(|node| node.kind() == SyntaxKind::Missing)
            .count(),
        1
    );

    let source = "f:\n  my\n  y";
    let (green, exit) = run(source);
    assert_eq!(green.to_string(), source);
    assert!(matches!(exit, Some(Err(Either::Right(_)))));
    let root = SyntaxNode::new_root(green);
    assert_eq!(
        root.descendants()
            .filter(|node| node.kind() == SyntaxKind::Statement)
            .count(),
        2
    );
}
