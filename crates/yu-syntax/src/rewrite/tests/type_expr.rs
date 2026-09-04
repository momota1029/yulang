use super::*;

fn top_type_expression(green: &GreenNode) -> SyntaxNode {
    SyntaxNode::new_root(green.clone())
        .children()
        .find(|node| node.kind() == SyntaxKind::TypeExpression)
        .expect("top-level type expression")
}

#[test]
fn type_expression_keeps_fixed_tails_in_source_order() {
    let source = "List(Int)::Result Arg -> Out -> Final";
    let (green, exit) = run_type(source);
    assert_eq!(green.to_string(), source);
    assert!(matches!(exit, Some(Err(Either::Right(_)))));

    let top = top_type_expression(&green);
    assert_eq!(
        top.children().map(|node| node.kind()).collect::<Vec<_>>(),
        [
            SyntaxKind::TypeCallTail,
            SyntaxKind::TypePathTail,
            SyntaxKind::TypeApplyArgument,
            SyntaxKind::TypeArrowTail,
        ]
    );
    let arrows = top
        .descendants()
        .filter(|node| node.kind() == SyntaxKind::TypeArrowTail)
        .count();
    assert_eq!(arrows, 2);
    assert_eq!(
        SyntaxNode::new_root(green)
            .descendants_with_tokens()
            .filter_map(|element| element.into_token())
            .map(|token| (token.kind(), token.text().to_owned()))
            .collect::<Vec<_>>(),
        [
            (SyntaxKind::Identifier, "List".to_owned()),
            (SyntaxKind::LParen, "(".to_owned()),
            (SyntaxKind::Identifier, "Int".to_owned()),
            (SyntaxKind::RParen, ")".to_owned()),
            (SyntaxKind::ColonColon, "::".to_owned()),
            (SyntaxKind::Identifier, "Result".to_owned()),
            (SyntaxKind::Whitespace, " ".to_owned()),
            (SyntaxKind::Identifier, "Arg".to_owned()),
            (SyntaxKind::Whitespace, " ".to_owned()),
            (SyntaxKind::Arrow, "->".to_owned()),
            (SyntaxKind::Whitespace, " ".to_owned()),
            (SyntaxKind::Identifier, "Out".to_owned()),
            (SyntaxKind::Whitespace, " ".to_owned()),
            (SyntaxKind::Arrow, "->".to_owned()),
            (SyntaxKind::Whitespace, " ".to_owned()),
            (SyntaxKind::Identifier, "Final".to_owned()),
        ]
    );
}

#[test]
fn type_expression_accepts_sigil_and_numeric_atoms_but_not_numeric_path_segments() {
    let source = "$value::'result _hidden 42";
    let (green, exit) = run_type(source);
    assert_eq!(green.to_string(), source);
    assert!(matches!(exit, Some(Err(Either::Right(_)))));

    let root = SyntaxNode::new_root(green);
    assert_eq!(
        root.descendants_with_tokens()
            .filter_map(|element| element.into_token())
            .map(|token| (token.kind(), token.text().to_owned()))
            .collect::<Vec<_>>(),
        [
            (SyntaxKind::SigilIdentifier, "$value".to_owned()),
            (SyntaxKind::ColonColon, "::".to_owned()),
            (SyntaxKind::SigilIdentifier, "'result".to_owned()),
            (SyntaxKind::Whitespace, " ".to_owned()),
            (SyntaxKind::SigilIdentifier, "_hidden".to_owned()),
            (SyntaxKind::Whitespace, " ".to_owned()),
            (SyntaxKind::Integer, "42".to_owned()),
        ]
    );
    assert_eq!(
        root.descendants()
            .filter(|node| node.kind() == SyntaxKind::TypeApplyArgument)
            .count(),
        2
    );
}

#[test]
fn type_apply_scope_keeps_adjacent_and_spaced_paths_distinct() {
    let adjacent = run_type("F A::B").0;
    let spaced = run_type("F A ::B").0;
    assert_eq!(adjacent.to_string(), "F A::B");
    assert_eq!(spaced.to_string(), "F A ::B");

    let adjacent_top = top_type_expression(&adjacent);
    let adjacent_apply = adjacent_top
        .children()
        .find(|node| node.kind() == SyntaxKind::TypeApplyArgument)
        .expect("adjacent apply");
    assert!(
        adjacent_apply
            .descendants()
            .any(|node| node.kind() == SyntaxKind::TypePathTail)
    );
    assert!(
        !adjacent_top
            .children()
            .any(|node| node.kind() == SyntaxKind::TypePathTail)
    );

    let spaced_top = top_type_expression(&spaced);
    assert!(
        spaced_top
            .children()
            .any(|node| node.kind() == SyntaxKind::TypePathTail)
    );
}

#[test]
fn type_call_and_group_keep_explicit_and_implicit_boundaries() {
    let source = "T(A, B; C) (D\nE)";
    let (green, exit) = run_type(source);
    assert_eq!(green.to_string(), source);
    assert!(matches!(exit, Some(Err(Either::Right(_)))));

    let top = top_type_expression(&green);
    let call = top
        .children()
        .find(|node| node.kind() == SyntaxKind::TypeCallTail)
        .expect("type call");
    assert_eq!(
        call.children()
            .filter(|node| node.kind() == SyntaxKind::TypeExpression)
            .count(),
        3
    );
    assert_eq!(
        call.children_with_tokens()
            .filter_map(|element| element.into_token())
            .map(|token| (token.kind(), token.text().to_owned()))
            .collect::<Vec<_>>(),
        [
            (SyntaxKind::LParen, "(".to_owned()),
            (SyntaxKind::Comma, ",".to_owned()),
            (SyntaxKind::Whitespace, " ".to_owned()),
            (SyntaxKind::Semicolon, ";".to_owned()),
            (SyntaxKind::Whitespace, " ".to_owned()),
            (SyntaxKind::RParen, ")".to_owned()),
        ]
    );
    let apply = top
        .children()
        .find(|node| node.kind() == SyntaxKind::TypeApplyArgument)
        .expect("group apply");
    let group = apply
        .descendants()
        .find(|node| node.kind() == SyntaxKind::ParenthesizedTypeGroup)
        .expect("parenthesized type group");
    assert_eq!(
        group
            .children()
            .filter(|node| node.kind() == SyntaxKind::TypeExpression)
            .count(),
        2
    );
    assert!(
        !SyntaxNode::new_root(green)
            .descendants()
            .any(|node| matches!(node.kind(), SyntaxKind::Missing | SyntaxKind::Error))
    );
}

#[test]
fn type_path_tail_recovers_its_mandatory_segment() {
    for (source, recovery) in [
        ("A::", SyntaxKind::Missing),
        ("A::123", SyntaxKind::Error),
        ("A::@Name", SyntaxKind::Error),
    ] {
        let (green, exit) = run_type(source);
        assert_eq!(green.to_string(), source, "{source:?}");
        assert!(matches!(exit, Some(Err(Either::Right(_)))), "{source:?}");
        let root = SyntaxNode::new_root(green);
        let path = root
            .descendants()
            .find(|node| node.kind() == SyntaxKind::TypePathTail)
            .expect("type path tail");
        assert_eq!(
            path.children()
                .filter(|node| node.kind() == recovery)
                .count(),
            1,
            "{source:?}"
        );
    }

    let (green, exit) = run_type("A::::Name");
    assert_eq!(green.to_string(), "A::::Name");
    assert!(matches!(exit, Some(Err(Either::Right(_)))));
    let root = SyntaxNode::new_root(green);
    assert_eq!(
        root.descendants()
            .filter(|node| node.kind() == SyntaxKind::TypePathTail)
            .count(),
        2
    );
    assert_eq!(
        root.descendants()
            .filter(|node| node.kind() == SyntaxKind::Missing)
            .count(),
        1
    );

    let (green, exit) = run_type("A:: ");
    assert_eq!(green.to_string(), "A:: ");
    assert!(matches!(exit, Some(Err(Either::Right(_)))));
    let root = SyntaxNode::new_root(green);
    let path = root
        .descendants()
        .find(|node| node.kind() == SyntaxKind::TypePathTail)
        .expect("type path tail");
    assert_eq!(
        path.descendants_with_tokens()
            .filter_map(|element| element.into_token())
            .map(|token| (token.kind(), token.text().to_owned()))
            .collect::<Vec<_>>(),
        [
            (SyntaxKind::ColonColon, "::".to_owned()),
            (SyntaxKind::Whitespace, " ".to_owned()),
        ]
    );
}

#[test]
fn type_arrow_tail_recovers_its_mandatory_rhs() {
    for (source, recovery) in [("A->", SyntaxKind::Missing), ("A->@B", SyntaxKind::Error)] {
        let (green, exit) = run_type(source);
        assert_eq!(green.to_string(), source, "{source:?}");
        assert!(matches!(exit, Some(Err(Either::Right(_)))), "{source:?}");
        let root = SyntaxNode::new_root(green);
        let arrow = root
            .descendants()
            .find(|node| node.kind() == SyntaxKind::TypeArrowTail)
            .expect("type arrow tail");
        assert_eq!(
            arrow
                .children()
                .filter(|node| node.kind() == recovery)
                .count(),
            1,
            "{source:?}"
        );
    }

    let (green, exit) = run_type("A->\n");
    assert_eq!(green.to_string(), "A->\n");
    assert!(matches!(exit, Some(Err(Either::Right(_)))));
    let root = SyntaxNode::new_root(green);
    let arrow = root
        .descendants()
        .find(|node| node.kind() == SyntaxKind::TypeArrowTail)
        .expect("type arrow tail");
    assert_eq!(
        arrow
            .descendants_with_tokens()
            .filter_map(|element| element.into_token())
            .map(|token| (token.kind(), token.text().to_owned()))
            .collect::<Vec<_>>(),
        [
            (SyntaxKind::Arrow, "->".to_owned()),
            (SyntaxKind::Newline, "\n".to_owned()),
        ]
    );
}

#[test]
fn type_delimited_owner_recovers_missing_items_and_close_at_eof() {
    for (source, owner, missing) in [
        ("T(", SyntaxKind::TypeCallTail, 1),
        ("(A", SyntaxKind::ParenthesizedTypeGroup, 1),
        ("T(A,", SyntaxKind::TypeCallTail, 2),
        ("T(,A)", SyntaxKind::TypeCallTail, 1),
        ("T(A,,B)", SyntaxKind::TypeCallTail, 1),
    ] {
        let (green, exit) = run_type(source);
        assert_eq!(green.to_string(), source, "{source:?}");
        assert!(matches!(exit, Some(Err(Either::Right(_)))), "{source:?}");
        let root = SyntaxNode::new_root(green);
        let owner = root
            .descendants()
            .find(|node| node.kind() == owner)
            .expect("type delimited owner");
        assert_eq!(
            owner
                .children()
                .filter(|node| node.kind() == SyntaxKind::Missing)
                .count(),
            missing,
            "{source:?}"
        );
    }

    let (green, exit) = run_type("T(A ");
    assert_eq!(green.to_string(), "T(A ");
    assert!(matches!(exit, Some(Err(Either::Right(_)))));
    let root = SyntaxNode::new_root(green);
    let call = root
        .descendants()
        .find(|node| node.kind() == SyntaxKind::TypeCallTail)
        .expect("type call tail");
    assert_eq!(
        call.descendants_with_tokens()
            .filter_map(|element| element.into_token())
            .map(|token| (token.kind(), token.text().to_owned()))
            .collect::<Vec<_>>(),
        [
            (SyntaxKind::LParen, "(".to_owned()),
            (SyntaxKind::Identifier, "A".to_owned()),
            (SyntaxKind::Whitespace, " ".to_owned()),
        ]
    );
}

#[test]
fn type_delimited_owner_retries_malformed_initial_items() {
    for (source, owner, recovered) in [
        ("T(@A)", SyntaxKind::TypeCallTail, "A"),
        ("(@A)", SyntaxKind::ParenthesizedTypeGroup, "A"),
        ("'[@A]", SyntaxKind::EffectRowType, "A"),
        ("T(@, A)", SyntaxKind::TypeCallTail, "A"),
    ] {
        let (green, exit) = run_type(source);
        assert_eq!(green.to_string(), source, "{source:?}");
        assert!(matches!(exit, Some(Err(Either::Right(_)))), "{source:?}");
        let root = SyntaxNode::new_root(green);
        let owner = root
            .descendants()
            .find(|node| node.kind() == owner)
            .expect("type delimited owner");
        assert_eq!(
            owner
                .children()
                .filter(|node| node.kind() == SyntaxKind::Error)
                .count(),
            1,
            "{source:?}"
        );
        assert!(
            owner
                .descendants_with_tokens()
                .filter_map(|element| element.into_token())
                .any(|token| token.kind() == SyntaxKind::Identifier && token.text() == recovered),
            "{source:?}"
        );
    }

    let (green, exit) = run_type("T(@");
    assert_eq!(green.to_string(), "T(@");
    assert!(matches!(exit, Some(Err(Either::Right(_)))));
    let root = SyntaxNode::new_root(green);
    let call = root
        .descendants()
        .find(|node| node.kind() == SyntaxKind::TypeCallTail)
        .expect("type call tail");
    assert_eq!(
        call.children()
            .filter(|node| matches!(node.kind(), SyntaxKind::Error | SyntaxKind::Missing))
            .count(),
        2
    );
}

#[test]
fn named_record_type_keeps_field_and_separator_ownership() {
    let source = "{a: A, b: List(Int)}";
    let (green, exit) = run_type(source);
    assert_eq!(green.to_string(), source);
    assert!(matches!(exit, Some(Err(Either::Right(_)))));

    let root = SyntaxNode::new_root(green);
    let record = root
        .descendants()
        .find(|node| node.kind() == SyntaxKind::NamedRecordType)
        .expect("named record type");
    assert_eq!(
        record
            .children()
            .filter(|node| node.kind() == SyntaxKind::TypeRecordField)
            .count(),
        2
    );
    assert_eq!(
        record
            .children_with_tokens()
            .filter_map(|element| element.into_token())
            .map(|token| (token.kind(), token.text().to_owned()))
            .collect::<Vec<_>>(),
        [
            (SyntaxKind::LBrace, "{".to_owned()),
            (SyntaxKind::Comma, ",".to_owned()),
            (SyntaxKind::Whitespace, " ".to_owned()),
            (SyntaxKind::RBrace, "}".to_owned()),
        ]
    );
}

#[test]
fn named_record_type_claims_a_same_line_complete_field_head_before_type_apply() {
    let (green, exit) = run_type("{a: F b: B}");
    assert_eq!(green.to_string(), "{a: F b: B}");
    assert!(matches!(exit, Some(Err(Either::Right(_)))));
    let record = SyntaxNode::new_root(green)
        .descendants()
        .find(|node| node.kind() == SyntaxKind::NamedRecordType)
        .expect("named record type");
    assert_eq!(
        record
            .children()
            .filter(|node| node.kind() == SyntaxKind::TypeRecordField)
            .count(),
        2
    );
    assert_eq!(
        record
            .descendants()
            .filter(|node| node.kind() == SyntaxKind::Missing)
            .count(),
        1
    );
    assert!(
        !record
            .descendants()
            .any(|node| node.kind() == SyntaxKind::TypeApplyArgument)
    );
    assert_eq!(
        record
            .children_with_tokens()
            .filter_map(|element| element.into_token())
            .filter(|token| token.kind() == SyntaxKind::Whitespace)
            .map(|token| token.text().to_owned())
            .collect::<Vec<_>>(),
        [" "]
    );

    let (green, exit) = run_type("{a: F B}");
    assert_eq!(green.to_string(), "{a: F B}");
    assert!(matches!(exit, Some(Err(Either::Right(_)))));
    let record = SyntaxNode::new_root(green)
        .descendants()
        .find(|node| node.kind() == SyntaxKind::NamedRecordType)
        .expect("named record type");
    assert_eq!(
        record
            .children()
            .filter(|node| node.kind() == SyntaxKind::TypeRecordField)
            .count(),
        1
    );
    assert_eq!(
        record
            .descendants()
            .filter(|node| node.kind() == SyntaxKind::Missing)
            .count(),
        0
    );
    assert_eq!(
        record
            .descendants()
            .filter(|node| node.kind() == SyntaxKind::TypeApplyArgument)
            .count(),
        1
    );
}

#[test]
fn named_record_type_recovers_leading_and_repeated_commas() {
    for (source, fields, missing) in [
        ("{,a: A}", 1, 1),
        ("{a: A,,b: B}", 2, 1),
        ("{,}", 0, 1),
        ("{a: A,}", 1, 0),
    ] {
        let (green, exit) = run_type(source);
        assert_eq!(green.to_string(), source, "{source:?}");
        assert!(matches!(exit, Some(Err(Either::Right(_)))), "{source:?}");
        let root = SyntaxNode::new_root(green);
        let record = root
            .descendants()
            .find(|node| node.kind() == SyntaxKind::NamedRecordType)
            .expect("named record type");
        assert_eq!(
            record
                .children()
                .filter(|node| node.kind() == SyntaxKind::TypeRecordField)
                .count(),
            fields,
            "{source:?}"
        );
        assert_eq!(
            record
                .descendants()
                .filter(|node| node.kind() == SyntaxKind::Missing)
                .count(),
            missing,
            "{source:?}"
        );
    }
}

#[test]
fn named_record_type_recovers_a_missing_field_before_eof_or_outer_close() {
    let (green, exit) = run_type("{a: A,");
    assert_eq!(green.to_string(), "{a: A,");
    assert!(matches!(exit, Some(Err(Either::Right(_)))));
    assert_eq!(
        SyntaxNode::new_root(green)
            .descendants()
            .filter(|node| node.kind() == SyntaxKind::Missing)
            .count(),
        2
    );

    let (green, exit) = run_type("{a: A,]");
    assert_eq!(green.to_string(), "{a: A,");
    assert!(matches!(
        exit,
        Some(Err(Either::Left(item)))
            if matches!(item.payload, Payload::Token(ref token) if token.kind == TokenKind::RBracket)
    ));
    assert_eq!(
        SyntaxNode::new_root(green)
            .descendants()
            .filter(|node| node.kind() == SyntaxKind::Missing)
            .count(),
        2
    );
}

#[test]
fn named_record_type_recovers_a_missing_close() {
    for (source, missing) in [("{", 1), ("{a: A", 1), ("{a: A,", 2)] {
        let (green, exit) = run_type(source);
        assert_eq!(green.to_string(), source, "{source:?}");
        assert!(matches!(exit, Some(Err(Either::Right(_)))), "{source:?}");
        assert_eq!(
            SyntaxNode::new_root(green)
                .descendants()
                .filter(|node| node.kind() == SyntaxKind::Missing)
                .count(),
            missing,
            "{source:?}"
        );
    }

    let (green, exit) = run_type("{a: A]");
    assert_eq!(green.to_string(), "{a: A");
    assert!(matches!(
        exit,
        Some(Err(Either::Left(item)))
            if matches!(item.payload, Payload::Token(ref token) if token.kind == TokenKind::RBracket)
    ));
    assert_eq!(
        SyntaxNode::new_root(green)
            .descendants()
            .filter(|node| node.kind() == SyntaxKind::Missing)
            .count(),
        1
    );
}

#[test]
fn named_record_type_retries_a_malformed_whole_field() {
    for (source, fields, error_text) in [
        ("{@ a: A}", 1, "@"),
        ("{@, b: B}", 1, "@"),
        ("{..A, b: B}", 1, "..A"),
        ("{@}", 0, "@"),
    ] {
        let (green, exit) = run_type(source);
        assert_eq!(green.to_string(), source, "{source:?}");
        assert!(matches!(exit, Some(Err(Either::Right(_)))), "{source:?}");
        let record = SyntaxNode::new_root(green)
            .descendants()
            .find(|node| node.kind() == SyntaxKind::NamedRecordType)
            .expect("named record type");
        assert_eq!(
            record
                .children()
                .filter(|node| node.kind() == SyntaxKind::TypeRecordField)
                .count(),
            fields,
            "{source:?}"
        );
        let error = record
            .children()
            .find(|node| node.kind() == SyntaxKind::Error)
            .expect("whole-field error");
        assert_eq!(error.text(), error_text, "{source:?}");
        assert!(
            !error
                .descendants()
                .any(|node| node.kind() == SyntaxKind::TypeRecordField),
            "{source:?}"
        );
    }
}

#[test]
fn named_record_whole_field_retry_keeps_qualified_newline_with_the_record() {
    let source = "{@\n  a: A}";
    let (green, exit) = run_type(source);
    assert_eq!(green.to_string(), source);
    assert!(matches!(exit, Some(Err(Either::Right(_)))));

    let record = SyntaxNode::new_root(green)
        .descendants()
        .find(|node| node.kind() == SyntaxKind::NamedRecordType)
        .expect("named record type");
    assert_eq!(
        record
            .children()
            .filter(|node| node.kind() == SyntaxKind::TypeRecordField)
            .count(),
        1
    );
    assert_eq!(
        record
            .children()
            .find(|node| node.kind() == SyntaxKind::Error)
            .expect("whole-field error")
            .text(),
        "@"
    );
    assert_eq!(
        record
            .children_with_tokens()
            .filter_map(|element| element.into_token())
            .filter(|token| token.kind() == SyntaxKind::Newline)
            .map(|token| token.text().to_owned())
            .collect::<Vec<_>>(),
        ["\n"]
    );
}

#[test]
fn named_record_field_retries_a_malformed_name_only_with_a_colon_skeleton() {
    for (source, error_text) in [
        ("{@: A}", "@"),
        ("{'a: A}", "'a"),
        ("{1: A}", "1"),
        ("{@ !: A}", "@ !"),
        ("{@ (): A}", "@ ()"),
    ] {
        let (green, exit) = run_type(source);
        assert_eq!(green.to_string(), source, "{source:?}");
        assert!(matches!(exit, Some(Err(Either::Right(_)))), "{source:?}");
        let root = SyntaxNode::new_root(green);
        let record = root
            .descendants()
            .find(|node| node.kind() == SyntaxKind::NamedRecordType)
            .expect("named record type");
        assert_eq!(
            record
                .children()
                .filter(|node| node.kind() == SyntaxKind::TypeRecordField)
                .count(),
            1,
            "{source:?}"
        );
        let field = record
            .children()
            .find(|node| node.kind() == SyntaxKind::TypeRecordField)
            .expect("type record field");
        assert_eq!(
            field
                .children()
                .filter(|node| node.kind() == SyntaxKind::Error)
                .count(),
            1,
            "{source:?}"
        );
        assert_eq!(
            field
                .children()
                .find(|node| node.kind() == SyntaxKind::Error)
                .expect("name error")
                .text(),
            error_text,
            "{source:?}"
        );
        assert_eq!(
            field
                .descendants()
                .filter(|node| node.kind() == SyntaxKind::Missing)
                .count(),
            0,
            "{source:?}"
        );
    }
}

#[test]
fn named_record_type_recovers_an_invalid_semicolon_separator() {
    for (source, fields) in [
        ("{a: A;b: B}", 2),
        ("{a: A; b: B}", 2),
        ("{a: A;}", 1),
        ("{;b: B}", 1),
        ("{;}", 0),
    ] {
        let (green, exit) = run_type(source);
        assert_eq!(green.to_string(), source, "{source:?}");
        assert!(matches!(exit, Some(Err(Either::Right(_)))), "{source:?}");
        let root = SyntaxNode::new_root(green);
        let record = root
            .descendants()
            .find(|node| node.kind() == SyntaxKind::NamedRecordType)
            .expect("named record type");
        assert_eq!(
            record
                .children()
                .filter(|node| node.kind() == SyntaxKind::TypeRecordField)
                .count(),
            fields,
            "{source:?}"
        );
        let error = record
            .children()
            .find(|node| node.kind() == SyntaxKind::Error)
            .expect("separator error");
        assert_eq!(error.text(), ";", "{source:?}");
    }

    let source = "{a: A; (\n) b: B}";
    let (green, exit) = run_type(source);
    assert_eq!(green.to_string(), source);
    assert!(matches!(exit, Some(Err(Either::Right(_)))));
    let record = SyntaxNode::new_root(green)
        .descendants()
        .find(|node| node.kind() == SyntaxKind::NamedRecordType)
        .expect("named record type");
    assert_eq!(
        record
            .children()
            .filter(|node| node.kind() == SyntaxKind::TypeRecordField)
            .count(),
        2
    );
    assert_eq!(
        record
            .children()
            .find(|node| node.kind() == SyntaxKind::Error)
            .expect("separator error")
            .text(),
        "; (\n)"
    );
}

#[test]
fn named_record_field_recovers_missing_colon_and_type() {
    for (source, fields) in [
        ("{a}", 1),
        ("{a, b: B}", 2),
        ("{a A}", 1),
        ("{a:}", 1),
        ("{a:\nb: B}", 2),
    ] {
        let (green, exit) = run_type(source);
        assert_eq!(green.to_string(), source, "{source:?}");
        assert!(matches!(exit, Some(Err(Either::Right(_)))), "{source:?}");
        let root = SyntaxNode::new_root(green);
        let record = root
            .descendants()
            .find(|node| node.kind() == SyntaxKind::NamedRecordType)
            .expect("named record type");
        assert_eq!(
            record
                .children()
                .filter(|node| node.kind() == SyntaxKind::TypeRecordField)
                .count(),
            fields,
            "{source:?}"
        );
        assert_eq!(
            record
                .descendants()
                .filter(|node| node.kind() == SyntaxKind::Missing)
                .count(),
            1,
            "{source:?}"
        );
    }

    let (green, exit) = run_type("{a for 'x: T}");
    assert!(matches!(exit, Some(Err(Either::Right(_)))));
    assert!(
        SyntaxNode::new_root(green)
            .descendants()
            .any(|node| node.kind() == SyntaxKind::ForallType)
    );
}

#[test]
fn named_record_field_recovers_a_missing_name_before_colon() {
    for (source, fields, missing) in [
        ("{: A}", 1, 1),
        ("{a: A, : B}", 2, 1),
        ("{a: A\n: B}", 2, 1),
        ("{:}", 1, 2),
    ] {
        let (green, exit) = run_type(source);
        assert_eq!(green.to_string(), source, "{source:?}");
        assert!(matches!(exit, Some(Err(Either::Right(_)))), "{source:?}");
        let root = SyntaxNode::new_root(green);
        let record = root
            .descendants()
            .find(|node| node.kind() == SyntaxKind::NamedRecordType)
            .expect("named record type");
        assert_eq!(
            record
                .children()
                .filter(|node| node.kind() == SyntaxKind::TypeRecordField)
                .count(),
            fields,
            "{source:?}"
        );
        assert_eq!(
            record
                .descendants()
                .filter(|node| node.kind() == SyntaxKind::Missing)
                .count(),
            missing,
            "{source:?}"
        );
    }
}

#[test]
fn named_record_field_retries_a_malformed_colon_slot() {
    for (source, error_text) in [("{a @ : B}", "@"), ("{a :: B}", "::"), ("{a @ B}", "@")] {
        let (green, exit) = run_type(source);
        assert_eq!(green.to_string(), source, "{source:?}");
        assert!(matches!(exit, Some(Err(Either::Right(_)))), "{source:?}");
        let root = SyntaxNode::new_root(green);
        let field = root
            .descendants()
            .find(|node| node.kind() == SyntaxKind::TypeRecordField)
            .expect("type record field");
        assert_eq!(
            field
                .children()
                .filter(|node| node.kind() == SyntaxKind::Error)
                .count(),
            1,
            "{source:?}"
        );
        let error = field
            .children()
            .find(|node| node.kind() == SyntaxKind::Error)
            .expect("colon error");
        assert_eq!(error.text(), error_text, "{source:?}");
        assert!(
            field
                .descendants_with_tokens()
                .filter_map(|element| element.into_token())
                .any(|token| token.kind() == SyntaxKind::Identifier && token.text() == "B"),
            "{source:?}"
        );
    }
}

#[test]
fn named_record_field_retries_a_malformed_type_slot() {
    for (source, fields) in [("{a: @ B}", 1), ("{a: @, b: B}", 2), ("{a: @\nb: B}", 2)] {
        let (green, exit) = run_type(source);
        assert_eq!(green.to_string(), source, "{source:?}");
        assert!(matches!(exit, Some(Err(Either::Right(_)))), "{source:?}");
        let root = SyntaxNode::new_root(green);
        let record = root
            .descendants()
            .find(|node| node.kind() == SyntaxKind::NamedRecordType)
            .expect("named record type");
        assert_eq!(
            record
                .children()
                .filter(|node| node.kind() == SyntaxKind::TypeRecordField)
                .count(),
            fields,
            "{source:?}"
        );
        let field = record
            .children()
            .find(|node| node.kind() == SyntaxKind::TypeRecordField)
            .expect("first type record field");
        let error = field
            .children()
            .find(|node| node.kind() == SyntaxKind::Error)
            .expect("type error");
        assert_eq!(error.text(), "@", "{source:?}");
        assert_eq!(
            field
                .descendants()
                .filter(|node| node.kind() == SyntaxKind::Missing)
                .count(),
            0,
            "{source:?}"
        );
    }
}

#[test]
fn named_record_type_accepts_layout_and_type_tails() {
    let layout = "{\n  a: A\n  b: B\n}";
    let (green, exit) = run_type(layout);
    assert_eq!(green.to_string(), layout);
    assert!(matches!(exit, Some(Err(Either::Right(_)))));
    let root = SyntaxNode::new_root(green);
    let record = root
        .descendants()
        .find(|node| node.kind() == SyntaxKind::NamedRecordType)
        .expect("named record type");
    assert_eq!(
        record
            .children()
            .filter(|node| node.kind() == SyntaxKind::TypeRecordField)
            .count(),
        2
    );

    let applied = run_type("F {a: A} -> Out").0;
    assert_eq!(applied.to_string(), "F {a: A} -> Out");
    let top = top_type_expression(&applied);
    assert!(
        top.children()
            .any(|node| node.kind() == SyntaxKind::TypeApplyArgument)
    );
    assert!(
        top.children()
            .any(|node| node.kind() == SyntaxKind::TypeArrowTail)
    );

    let (adjacent, exit) = run_type("F{a:A}");
    assert_eq!(adjacent.to_string(), "F");
    assert!(matches!(
        exit,
        Some(Err(Either::Left(item)))
            if matches!(item.payload, Payload::Token(ref token) if token.kind == TokenKind::LBrace)
    ));
    assert!(
        !SyntaxNode::new_root(adjacent)
            .descendants()
            .any(|node| node.kind() == SyntaxKind::NamedRecordType)
    );
}

#[test]
fn forall_type_is_contextual_terminal_primary() {
    let source = "for 'a: A -> A";
    let (green, exit) = run_type(source);
    assert_eq!(green.to_string(), source);
    assert!(matches!(exit, Some(Err(Either::Right(_)))));
    let top = top_type_expression(&green);
    assert_eq!(
        top.children().map(|node| node.kind()).collect::<Vec<_>>(),
        [SyntaxKind::ForallType]
    );
    let forall = top
        .children()
        .find(|node| node.kind() == SyntaxKind::ForallType)
        .expect("forall type");
    assert_eq!(
        forall
            .children()
            .filter(|node| node.kind() == SyntaxKind::ForallTypeBinder)
            .count(),
        1
    );
    assert!(
        forall
            .descendants()
            .any(|node| node.kind() == SyntaxKind::TypeArrowTail)
    );

    let layout = "for\n  'a\n  'b:\n    Pair('a, 'b)";
    let (green, exit) = run_type(layout);
    assert_eq!(green.to_string(), layout);
    assert!(matches!(exit, Some(Err(Either::Right(_)))));
    let root = SyntaxNode::new_root(green);
    assert_eq!(
        root.descendants()
            .filter(|node| node.kind() == SyntaxKind::ForallTypeBinder)
            .count(),
        2
    );

    for source in ["(for 'a: T)", "F(for 'a: T)", "A -> for 'a: T"] {
        let (green, exit) = run_type(source);
        assert_eq!(green.to_string(), source, "{source:?}");
        assert!(matches!(exit, Some(Err(Either::Right(_)))), "{source:?}");
        assert_eq!(
            SyntaxNode::new_root(green)
                .descendants()
                .filter(|node| node.kind() == SyntaxKind::ForallType)
                .count(),
            1,
            "{source:?}"
        );
    }

    let grouped = run_type("(for 'a: T)::Result").0;
    let top = top_type_expression(&grouped);
    assert!(
        top.children()
            .any(|node| node.kind() == SyntaxKind::ParenthesizedTypeGroup)
    );
    assert!(
        top.children()
            .any(|node| node.kind() == SyntaxKind::TypePathTail)
    );
}

#[test]
fn forall_type_recovers_clean_mandatory_slots_without_cascading() {
    for source in ["for", "for 'a", "for 'a:", "for'a: T", "for 'a T", "for: T"] {
        let (green, exit) = run_type(source);
        assert_eq!(green.to_string(), source, "{source:?}");
        assert!(matches!(exit, Some(Err(Either::Right(_)))), "{source:?}");
        let forall = SyntaxNode::new_root(green)
            .descendants()
            .find(|node| node.kind() == SyntaxKind::ForallType)
            .expect("forall type");
        assert_eq!(
            forall
                .descendants()
                .filter(|node| node.kind() == SyntaxKind::Missing)
                .count(),
            1,
            "{source:?}"
        );
    }

    let (green, exit) = run_type("for\n");
    assert_eq!(green.to_string(), "for\n");
    assert!(matches!(exit, Some(Err(Either::Right(_)))));
    let root = SyntaxNode::new_root(green);
    let forall = root
        .descendants()
        .find(|node| node.kind() == SyntaxKind::ForallType)
        .expect("forall type");
    assert!(
        !forall
            .children_with_tokens()
            .filter_map(|element| element.into_token())
            .any(|token| token.kind() == SyntaxKind::Newline)
    );
    assert!(
        root.children_with_tokens()
            .filter_map(|element| element.into_token())
            .any(|token| token.kind() == SyntaxKind::Newline && token.text() == "\n")
    );
}

#[test]
fn forall_type_recovers_root_separators_as_its_own_malformed_phase() {
    for (source, separator, binders) in [
        ("for, 'a: T", ",", 2),
        ("for; 'a: T", ";", 2),
        ("for 'a, 'b: T", ",", 3),
        ("for 'a; 'b: T", ";", 3),
    ] {
        let (green, exit) = run_type(source);
        assert_eq!(green.to_string(), source, "{source:?}");
        assert!(matches!(exit, Some(Err(Either::Right(_)))), "{source:?}");
        let forall = SyntaxNode::new_root(green)
            .descendants()
            .find(|node| node.kind() == SyntaxKind::ForallType)
            .expect("forall type");
        let errors = forall
            .descendants()
            .filter(|node| node.kind() == SyntaxKind::Error)
            .collect::<Vec<_>>();
        assert_eq!(
            errors
                .iter()
                .map(|node| node.text().to_string())
                .collect::<Vec<_>>(),
            [separator],
            "{source:?}"
        );
        assert_eq!(
            errors[0].parent().map(|node| node.kind()),
            Some(SyntaxKind::ForallTypeBinder),
            "{source:?}"
        );
        assert_eq!(
            forall
                .descendants()
                .filter(|node| node.kind() == SyntaxKind::Missing)
                .count(),
            0,
            "{source:?}"
        );
        assert_eq!(
            forall
                .children()
                .filter(|node| node.kind() == SyntaxKind::ForallTypeBinder)
                .count(),
            binders,
            "{source:?}"
        );
    }
}

#[test]
fn forall_type_separator_recovery_keeps_first_binder_and_continuation_phases_distinct() {
    for (source, consumed, separator) in [("for, T", "for,", ","), ("for; T", "for;", ";")] {
        let (green, exit) = run_type(source);
        assert_eq!(green.to_string(), consumed, "{source:?}");
        assert!(matches!(
            exit,
            Some(Err(Either::Left(item)))
                if matches!(item.payload, Payload::Token(ref token) if token.kind == TokenKind::Identifier && token.text.as_ref() == "T")
                    && item.leading.0.iter().any(|trivia| trivia.kind == TriviaKind::Whitespace && trivia.text.as_ref() == " ")
        ));
        let forall = SyntaxNode::new_root(green)
            .descendants()
            .find(|node| node.kind() == SyntaxKind::ForallType)
            .expect("forall type");
        let error = forall
            .descendants()
            .find(|node| node.kind() == SyntaxKind::Error)
            .expect("separator error");
        assert_eq!(error.text().to_string(), separator, "{source:?}");
        assert_eq!(
            error.parent().map(|node| node.kind()),
            Some(SyntaxKind::ForallTypeBinder),
            "{source:?}"
        );
        assert!(
            !forall
                .descendants()
                .any(|node| node.kind() == SyntaxKind::TypeExpression),
            "{source:?}"
        );
        assert!(
            !forall
                .descendants()
                .any(|node| node.kind() == SyntaxKind::Missing),
            "{source:?}"
        );
    }

    for (source, separator) in [("for 'a, T", ","), ("for 'a; T", ";")] {
        let (green, exit) = run_type(source);
        assert_eq!(green.to_string(), source, "{source:?}");
        assert!(matches!(exit, Some(Err(Either::Right(_)))), "{source:?}");
        let forall = SyntaxNode::new_root(green)
            .descendants()
            .find(|node| node.kind() == SyntaxKind::ForallType)
            .expect("forall type");
        let error = forall
            .descendants()
            .find(|node| node.kind() == SyntaxKind::Error)
            .expect("separator error");
        assert_eq!(error.text().to_string(), separator, "{source:?}");
        assert_eq!(
            error.parent().map(|node| node.kind()),
            Some(SyntaxKind::ForallTypeBinder),
            "{source:?}"
        );
        assert_eq!(
            forall
                .descendants()
                .filter(|node| node.kind() == SyntaxKind::Missing)
                .count(),
            1,
            "{source:?}"
        );
        assert!(
            forall
                .descendants()
                .any(|node| node.kind() == SyntaxKind::TypeExpression),
            "{source:?}"
        );
    }
}

#[test]
fn forall_type_handoffs_active_owner_separators_without_absorbing_trivia() {
    for source in ["F(for, A)", "F(for; A)", "F(for 'a, B)", "F(for 'a; B)"] {
        let (green, exit) = run_type(source);
        assert_eq!(green.to_string(), source, "{source:?}");
        assert!(matches!(exit, Some(Err(Either::Right(_)))), "{source:?}");
        let root = SyntaxNode::new_root(green);
        let forall = root
            .descendants()
            .find(|node| node.kind() == SyntaxKind::ForallType)
            .expect("forall type");
        assert!(
            !forall
                .descendants()
                .any(|node| node.kind() == SyntaxKind::Error),
            "{source:?}"
        );
        assert_eq!(
            forall
                .descendants()
                .filter(|node| node.kind() == SyntaxKind::Missing)
                .count(),
            1,
            "{source:?}"
        );
        assert!(
            !forall
                .children_with_tokens()
                .filter_map(|element| element.into_token())
                .any(|token| { matches!(token.kind(), SyntaxKind::Comma | SyntaxKind::Semicolon) }),
            "{source:?}"
        );
        let call = root
            .descendants()
            .find(|node| node.kind() == SyntaxKind::TypeCallTail)
            .expect("type call");
        assert_eq!(
            call.descendants_with_tokens()
                .filter_map(|element| element.into_token())
                .filter(|token| matches!(token.kind(), SyntaxKind::Comma | SyntaxKind::Semicolon))
                .count(),
            1,
            "{source:?}"
        );
    }

    let source = "F(for 'a /* gap */, B)";
    let (green, exit) = run_type(source);
    assert_eq!(green.to_string(), source);
    assert!(matches!(exit, Some(Err(Either::Right(_)))));
    let root = SyntaxNode::new_root(green);
    let forall = root
        .descendants()
        .find(|node| node.kind() == SyntaxKind::ForallType)
        .expect("forall type");
    let call = root
        .descendants()
        .find(|node| node.kind() == SyntaxKind::TypeCallTail)
        .expect("type call");
    assert!(!forall.text().to_string().contains("/* gap */"));
    assert!(call.text().to_string().contains("/* gap */"));
}

#[test]
fn forall_type_body_separators_follow_the_active_owner() {
    for (source, separator) in [("for 'a: , T", ","), ("for 'a: ; T", ";")] {
        let (green, exit) = run_type(source);
        assert_eq!(green.to_string(), source, "{source:?}");
        assert!(matches!(exit, Some(Err(Either::Right(_)))), "{source:?}");
        let forall = SyntaxNode::new_root(green)
            .descendants()
            .find(|node| node.kind() == SyntaxKind::ForallType)
            .expect("forall type");
        assert_eq!(
            forall
                .descendants()
                .filter(|node| node.kind() == SyntaxKind::Error)
                .map(|node| node.text().to_string())
                .collect::<Vec<_>>(),
            [separator],
            "{source:?}"
        );
        assert!(
            !forall
                .descendants()
                .any(|node| node.kind() == SyntaxKind::Missing),
            "{source:?}"
        );
    }

    for source in ["F(for 'a: , T)", "F(for 'a: ; T)"] {
        let (green, exit) = run_type(source);
        assert_eq!(green.to_string(), source, "{source:?}");
        assert!(matches!(exit, Some(Err(Either::Right(_)))), "{source:?}");
        let root = SyntaxNode::new_root(green);
        let forall = root
            .descendants()
            .find(|node| node.kind() == SyntaxKind::ForallType)
            .expect("forall type");
        assert!(
            !forall
                .descendants()
                .any(|node| node.kind() == SyntaxKind::Error),
            "{source:?}"
        );
        assert_eq!(
            forall
                .descendants()
                .filter(|node| node.kind() == SyntaxKind::Missing)
                .count(),
            1,
            "{source:?}"
        );
    }
}

#[test]
fn forall_type_handoffs_record_and_variant_payload_separators() {
    for (source, separator, record_error) in [
        ("{a: for 'a, b: B}", ",", None),
        ("{a: for 'a; b: B}", ";", Some(";")),
    ] {
        let (green, exit) = run_type(source);
        assert_eq!(green.to_string(), source, "{source:?}");
        assert!(matches!(exit, Some(Err(Either::Right(_)))), "{source:?}");
        let root = SyntaxNode::new_root(green);
        let forall = root
            .descendants()
            .find(|node| node.kind() == SyntaxKind::ForallType)
            .expect("forall type");
        assert!(
            !forall
                .descendants()
                .any(|node| node.kind() == SyntaxKind::Error),
            "{source:?}"
        );
        assert_eq!(
            forall
                .descendants()
                .filter(|node| node.kind() == SyntaxKind::Missing)
                .count(),
            1,
            "{source:?}"
        );
        assert!(
            !forall
                .children_with_tokens()
                .filter_map(|element| element.into_token())
                .any(|token| { matches!(token.kind(), SyntaxKind::Comma | SyntaxKind::Semicolon) }),
            "{source:?}"
        );
        let record = root
            .descendants()
            .find(|node| node.kind() == SyntaxKind::NamedRecordType)
            .expect("named record type");
        assert_eq!(
            record
                .children()
                .filter(|node| node.kind() == SyntaxKind::TypeRecordField)
                .count(),
            2,
            "{source:?}"
        );
        assert_eq!(
            record
                .descendants()
                .filter(|node| node.kind() == SyntaxKind::Error)
                .map(|node| node.text().to_string())
                .collect::<Vec<_>>(),
            record_error.into_iter().collect::<Vec<_>>(),
            "{source:?}"
        );
        assert_eq!(
            record
                .descendants_with_tokens()
                .filter_map(|element| element.into_token())
                .filter(|token| matches!(token.kind(), SyntaxKind::Comma | SyntaxKind::Semicolon))
                .map(|token| token.text().to_string())
                .collect::<Vec<_>>(),
            [separator],
            "{source:?}"
        );
    }

    let (green, exit) = run_type(":{A for 'a, B}");
    assert_eq!(green.to_string(), ":{A for 'a, B}");
    assert!(matches!(exit, Some(Err(Either::Right(_)))));
    let root = SyntaxNode::new_root(green);
    let forall = root
        .descendants()
        .find(|node| node.kind() == SyntaxKind::ForallType)
        .expect("forall type");
    assert!(
        !forall
            .descendants()
            .any(|node| node.kind() == SyntaxKind::Error)
    );
    assert_eq!(
        forall
            .descendants()
            .filter(|node| node.kind() == SyntaxKind::Missing)
            .count(),
        1
    );
    assert_eq!(
        root.descendants()
            .filter(|node| node.kind() == SyntaxKind::PolymorphicVariantTag)
            .count(),
        2
    );
}

#[test]
fn forall_type_recovers_malformed_phase_runs_and_retries() {
    for (source, expected_error, expected_missing, expected_binders) in [
        ("for @", "@", 0, 1),
        ("for T", "T", 0, 1),
        ("for @ 'a: T", "@", 0, 2),
        ("for @: T", "@", 0, 1),
        ("for 'a @", "@", 0, 1),
        ("for 'a @ 'b: T", "@", 0, 3),
        ("for 'a @: T", "@", 0, 1),
        ("for 'a @ T", "@", 0, 1),
        ("for 'a: @", "@", 0, 1),
        ("for 'a: @ T", "@", 0, 1),
    ] {
        let (green, exit) = run_type(source);
        assert_eq!(green.to_string(), source, "{source:?}");
        assert!(matches!(exit, Some(Err(Either::Right(_)))), "{source:?}");
        let forall = SyntaxNode::new_root(green)
            .descendants()
            .find(|node| node.kind() == SyntaxKind::ForallType)
            .expect("forall type");
        assert_eq!(
            forall
                .descendants()
                .filter(|node| node.kind() == SyntaxKind::Error)
                .map(|node| node.text().to_string())
                .collect::<Vec<_>>(),
            [expected_error],
            "{source:?}"
        );
        assert_eq!(
            forall
                .descendants()
                .filter(|node| node.kind() == SyntaxKind::Missing)
                .count(),
            expected_missing,
            "{source:?}"
        );
        assert_eq!(
            forall
                .children()
                .filter(|node| node.kind() == SyntaxKind::ForallTypeBinder)
                .count(),
            expected_binders,
            "{source:?}"
        );
    }

    let first_binder = run_type("for @ 'a: T").0;
    let first_binder = SyntaxNode::new_root(first_binder)
        .descendants()
        .find(|node| node.kind() == SyntaxKind::ForallTypeBinder)
        .expect("recovered first binder");
    assert!(
        first_binder
            .descendants()
            .any(|node| node.kind() == SyntaxKind::Error)
    );

    let malformed_colon = run_type("for 'a @: T").0;
    let malformed_colon = SyntaxNode::new_root(malformed_colon)
        .descendants()
        .find(|node| node.kind() == SyntaxKind::ForallType)
        .expect("forall type");
    assert!(
        malformed_colon
            .children()
            .any(|node| node.kind() == SyntaxKind::Error)
    );

    let (green, exit) = run_type("for 'a @\nT");
    assert_eq!(green.to_string(), "for 'a @");
    assert!(matches!(
        exit,
        Some(Err(Either::Left(item)))
            if matches!(item.payload, Payload::Token(ref token) if token.kind == TokenKind::Identifier && token.text.as_ref() == "T")
                && item.leading.0.iter().any(|trivia| trivia.kind == TriviaKind::Newline && trivia.text.as_ref() == "\n")
    ));
    let root = SyntaxNode::new_root(green);
    let forall = root
        .descendants()
        .find(|node| node.kind() == SyntaxKind::ForallType)
        .expect("forall type");
    assert!(
        !forall
            .children_with_tokens()
            .filter_map(|element| element.into_token())
            .any(|token| token.kind() == SyntaxKind::Newline)
    );

    let deeper = run_type("for\n  'a @\n  'b: T").0;
    let deeper = SyntaxNode::new_root(deeper);
    assert_eq!(
        deeper
            .descendants()
            .filter(|node| node.kind() == SyntaxKind::ForallTypeBinder)
            .count(),
        3
    );

    let nested = run_type("for (@: T) 'a: T").0;
    let nested = SyntaxNode::new_root(nested);
    assert_eq!(
        nested
            .descendants()
            .filter(|node| node.kind() == SyntaxKind::Error)
            .map(|node| node.text().to_string())
            .collect::<Vec<_>>(),
        ["(@: T)"]
    );

    let nested_newline = run_type("for (@\n) 'a: T").0;
    let nested_newline = SyntaxNode::new_root(nested_newline);
    assert_eq!(
        nested_newline
            .descendants()
            .filter(|node| node.kind() == SyntaxKind::Error)
            .map(|node| node.text().to_string())
            .collect::<Vec<_>>(),
        ["(@\n)"]
    );
    assert_eq!(
        nested_newline
            .descendants()
            .filter(|node| node.kind() == SyntaxKind::ForallTypeBinder)
            .count(),
        2
    );

    for source in ["for 'a @ (@: T)", "for 'a @ ('b)"] {
        let (green, _) = run_type(source);
        assert_eq!(green.to_string(), source, "{source:?}");
        let forall = SyntaxNode::new_root(green)
            .descendants()
            .find(|node| node.kind() == SyntaxKind::ForallType)
            .expect("forall type");
        assert!(
            !forall
                .children_with_tokens()
                .filter_map(|element| element.into_token())
                .any(|token| token.kind() == SyntaxKind::Colon),
            "{source:?}"
        );
    }
}

#[test]
fn forall_type_does_not_reclassify_type_apply_for() {
    for source in ["forx 'a", "forall 'a", "for_ 'a"] {
        let (green, exit) = run_type(source);
        assert_eq!(green.to_string(), source, "{source:?}");
        assert!(matches!(exit, Some(Err(Either::Right(_)))), "{source:?}");
        assert!(
            !SyntaxNode::new_root(green)
                .descendants()
                .any(|node| node.kind() == SyntaxKind::ForallType),
            "{source:?}"
        );
    }

    let (green, exit) = run_type("F for 'a: T");
    assert_eq!(green.to_string(), "F for 'a");
    assert!(matches!(
        exit,
        Some(Err(Either::Left(item)))
            if matches!(item.payload, Payload::Token(ref token) if token.kind == TokenKind::Colon)
    ));
    assert!(
        !SyntaxNode::new_root(green)
            .descendants()
            .any(|node| node.kind() == SyntaxKind::ForallType)
    );
}

#[test]
fn effect_row_type_keeps_its_compound_opener_and_items() {
    for (source, item_kind) in [
        ("'[]", None),
        ("'[e]", Some(SyntaxKind::Identifier)),
        ("'['e]", Some(SyntaxKind::SigilIdentifier)),
    ] {
        let (green, exit) = run_type(source);
        assert_eq!(green.to_string(), source, "{source:?}");
        assert!(matches!(exit, Some(Err(Either::Right(_)))), "{source:?}");
        let root = SyntaxNode::new_root(green);
        let row = root
            .descendants()
            .find(|node| node.kind() == SyntaxKind::EffectRowType)
            .expect("effect row type");
        assert_eq!(
            row.descendants_with_tokens()
                .filter_map(|element| element.into_token())
                .filter(|token| {
                    matches!(
                        token.kind(),
                        SyntaxKind::Apostrophe | SyntaxKind::LBracket | SyntaxKind::RBracket
                    )
                })
                .map(|token| (token.kind(), token.text().to_owned()))
                .collect::<Vec<_>>(),
            [
                (SyntaxKind::Apostrophe, "'".to_owned()),
                (SyntaxKind::LBracket, "[".to_owned()),
                (SyntaxKind::RBracket, "]".to_owned()),
            ],
            "{source:?}"
        );
        assert_eq!(
            row.descendants_with_tokens()
                .filter_map(|element| element.into_token())
                .filter(|token| {
                    matches!(
                        token.kind(),
                        SyntaxKind::Identifier | SyntaxKind::SigilIdentifier
                    )
                })
                .map(|token| token.kind())
                .collect::<Vec<_>>(),
            item_kind.into_iter().collect::<Vec<_>>(),
            "{source:?}"
        );
    }
}

#[test]
fn effect_row_type_composes_with_layout_and_tails() {
    let layout = "'[\n  A, B;\n  C\n  D\n]";
    let (green, exit) = run_type(layout);
    assert_eq!(green.to_string(), layout);
    assert!(matches!(exit, Some(Err(Either::Right(_)))));
    let root = SyntaxNode::new_root(green);
    let row = root
        .descendants()
        .find(|node| node.kind() == SyntaxKind::EffectRowType)
        .expect("effect row type");
    assert_eq!(
        row.children()
            .filter(|node| node.kind() == SyntaxKind::TypeExpression)
            .count(),
        4
    );

    let (green, exit) = run_type("Foo '['e] -> Out");
    assert_eq!(green.to_string(), "Foo '['e] -> Out");
    assert!(matches!(exit, Some(Err(Either::Right(_)))));
    let top = top_type_expression(&green);
    assert!(
        top.children()
            .any(|node| node.kind() == SyntaxKind::TypeApplyArgument)
    );
    assert!(
        top.children()
            .any(|node| node.kind() == SyntaxKind::TypeArrowTail)
    );

    let path = run_type("'[e]::Result").0;
    assert!(
        top_type_expression(&path)
            .children()
            .any(|node| node.kind() == SyntaxKind::TypePathTail)
    );

    for source in ["'", "' [e]", "'/*c*/[e]"] {
        let (green, exit) = run_type(source);
        assert_eq!(green.to_string(), "", "{source:?}");
        assert!(exit.is_none(), "{source:?}");
    }
}

#[test]
fn polymorphic_variant_type_keeps_two_level_boundaries() {
    for (source, tags, payloads) in [
        (":{}", 0, 0),
        (":{A Int, B}", 2, 1),
        (":{A Int Bool}", 1, 2),
        (":{A Int\nB}", 2, 1),
        (":{A,}", 1, 0),
    ] {
        let (green, exit) = run_type(source);
        assert_eq!(green.to_string(), source, "{source:?}");
        assert!(matches!(exit, Some(Err(Either::Right(_)))), "{source:?}");
        let root = SyntaxNode::new_root(green);
        let variant = root
            .descendants()
            .find(|node| node.kind() == SyntaxKind::PolymorphicVariantType)
            .expect("polymorphic variant type");
        assert_eq!(
            variant
                .children()
                .filter(|node| node.kind() == SyntaxKind::PolymorphicVariantTag)
                .count(),
            tags,
            "{source:?}"
        );
        assert_eq!(
            variant
                .descendants()
                .filter(|node| node.kind() == SyntaxKind::PolymorphicVariantPayload)
                .count(),
            payloads,
            "{source:?}"
        );
    }

    let nested = ":{\n  A Pair(\n    Int,\n    Bool\n  )\n  B\n}";
    let (green, exit) = run_type(nested);
    assert_eq!(green.to_string(), nested);
    assert!(matches!(exit, Some(Err(Either::Right(_)))));
    let variant = SyntaxNode::new_root(green)
        .descendants()
        .find(|node| node.kind() == SyntaxKind::PolymorphicVariantType)
        .expect("polymorphic variant type");
    assert_eq!(
        variant
            .children()
            .filter(|node| node.kind() == SyntaxKind::PolymorphicVariantTag)
            .count(),
        2
    );

    let (green, exit) = run_type(":{A [e] T X}");
    assert_eq!(green.to_string(), ":{A [e] T X}");
    assert!(matches!(exit, Some(Err(Either::Right(_)))));
    let variant = SyntaxNode::new_root(green)
        .descendants()
        .find(|node| node.kind() == SyntaxKind::PolymorphicVariantType)
        .expect("polymorphic variant type");
    assert_eq!(
        variant
            .descendants()
            .filter(|node| node.kind() == SyntaxKind::PolymorphicVariantPayload)
            .count(),
        2
    );
}

#[test]
fn polymorphic_variant_type_recovers_outer_tag_positions() {
    for (source, tags, missing) in [
        (":{,A}", 1, 1),
        (":{,,A}", 1, 2),
        (":{A,,B}", 2, 1),
        (":{,}", 0, 1),
        (":{A,}", 1, 0),
        (":{A,,}", 1, 1),
    ] {
        let (green, exit) = run_type(source);
        assert_eq!(green.to_string(), source, "{source:?}");
        assert!(matches!(exit, Some(Err(Either::Right(_)))), "{source:?}");
        let variant = SyntaxNode::new_root(green)
            .descendants()
            .find(|node| node.kind() == SyntaxKind::PolymorphicVariantType)
            .expect("polymorphic variant type");
        assert_eq!(
            variant
                .children()
                .filter(|node| node.kind() == SyntaxKind::PolymorphicVariantTag)
                .count(),
            tags,
            "{source:?}"
        );
        assert_eq!(
            variant
                .descendants()
                .filter(|node| node.kind() == SyntaxKind::Missing)
                .count(),
            missing,
            "{source:?}"
        );
    }
}

#[test]
fn polymorphic_variant_type_recovers_non_identifier_tag_primaries() {
    for (source, tag_text, payloads) in [
        (":{123}", "123", 0),
        (":{123 Int}", "123", 1),
        (":{for 'a: T}", "for 'a: T", 0),
        (":{:{A} B}", ":{A}", 1),
    ] {
        let (green, exit) = run_type(source);
        assert_eq!(green.to_string(), source, "{source:?}");
        assert!(matches!(exit, Some(Err(Either::Right(_)))), "{source:?}");
        let variant = SyntaxNode::new_root(green)
            .descendants()
            .find(|node| node.kind() == SyntaxKind::PolymorphicVariantType)
            .expect("polymorphic variant type");
        let tags = variant
            .children()
            .filter(|node| node.kind() == SyntaxKind::PolymorphicVariantTag)
            .collect::<Vec<_>>();
        assert_eq!(tags.len(), 1, "{source:?}");
        let tag = &tags[0];
        let errors = tag
            .children()
            .filter(|node| node.kind() == SyntaxKind::Error)
            .collect::<Vec<_>>();
        assert_eq!(errors.len(), 1, "{source:?}");
        let error = &errors[0];
        assert_eq!(error.text().to_string(), tag_text, "{source:?}");
        assert_eq!(
            error
                .children()
                .filter(|node| node.kind() == SyntaxKind::TypeExpression)
                .count(),
            1,
            "{source:?}"
        );
        assert!(
            !tag.descendants()
                .any(|node| node.kind() == SyntaxKind::Missing),
            "{source:?}"
        );
        assert_eq!(
            tag.descendants()
                .filter(|node| node.kind() == SyntaxKind::PolymorphicVariantPayload)
                .count(),
            payloads,
            "{source:?}"
        );
    }

    for source in [":{123, A}", ":{123\nA}"] {
        let (green, exit) = run_type(source);
        assert_eq!(green.to_string(), source, "{source:?}");
        assert!(matches!(exit, Some(Err(Either::Right(_)))), "{source:?}");
        let variant = SyntaxNode::new_root(green)
            .descendants()
            .find(|node| node.kind() == SyntaxKind::PolymorphicVariantType)
            .expect("polymorphic variant type");
        assert_eq!(
            variant
                .children()
                .filter(|node| node.kind() == SyntaxKind::PolymorphicVariantTag)
                .count(),
            2,
            "{source:?}"
        );
        assert!(
            !variant
                .descendants()
                .any(|node| node.kind() == SyntaxKind::Missing),
            "{source:?}"
        );
    }

    let (green, exit) = run_type(":{123]}");
    assert_eq!(green.to_string(), ":{123]}");
    assert!(matches!(exit, Some(Err(Either::Right(_)))));
    let variant = SyntaxNode::new_root(green)
        .descendants()
        .find(|node| node.kind() == SyntaxKind::PolymorphicVariantType)
        .expect("polymorphic variant type");
    assert_eq!(
        variant
            .descendants()
            .filter(|node| node.kind() == SyntaxKind::Error)
            .map(|node| node.text().to_string())
            .collect::<Vec<_>>(),
        ["123", "]"]
    );
}

#[test]
fn polymorphic_variant_type_recovers_malformed_tag_runs() {
    fn polymorphic_variant_node(green: GreenNode) -> SyntaxNode {
        SyntaxNode::new_root(green)
            .descendants()
            .find(|node| node.kind() == SyntaxKind::PolymorphicVariantType)
            .expect("polymorphic variant type")
    }

    for (source, tags, missing) in [
        (":{@}", 1, 0),
        (":{@", 1, 1),
        (":{@A}", 1, 0),
        (":{A@,B}", 3, 0),
        (":{@\nA}", 2, 0),
        (":{@]}", 1, 0),
    ] {
        let (green, exit) = run_type(source);
        assert_eq!(green.to_string(), source, "{source:?}");
        assert!(matches!(exit, Some(Err(Either::Right(_)))), "{source:?}");
        let variant = polymorphic_variant_node(green);
        assert_eq!(
            variant
                .children()
                .filter(|node| node.kind() == SyntaxKind::PolymorphicVariantTag)
                .count(),
            tags,
            "{source:?}"
        );
        assert_eq!(
            variant
                .descendants()
                .filter(|node| node.kind() == SyntaxKind::Missing)
                .count(),
            missing,
            "{source:?}"
        );
        assert_eq!(
            variant
                .descendants()
                .filter(|node| node.kind() == SyntaxKind::Error)
                .next()
                .expect("malformed tag error")
                .text()
                .to_string(),
            "@",
            "{source:?}"
        );
    }

    let (green, exit) = run_type(":{@123 Int}");
    assert_eq!(green.to_string(), ":{@123 Int}");
    assert!(matches!(exit, Some(Err(Either::Right(_)))));
    let variant = polymorphic_variant_node(green);
    let tags = variant
        .children()
        .filter(|node| node.kind() == SyntaxKind::PolymorphicVariantTag)
        .collect::<Vec<_>>();
    assert_eq!(tags.len(), 1);
    let errors = tags[0]
        .children()
        .filter(|node| node.kind() == SyntaxKind::Error)
        .collect::<Vec<_>>();
    assert_eq!(
        errors
            .iter()
            .map(|node| node.text().to_string())
            .collect::<Vec<_>>(),
        ["@", "123"]
    );
    assert!(
        errors[0]
            .children()
            .all(|node| node.kind() != SyntaxKind::TypeExpression)
    );
    assert_eq!(
        errors[1]
            .children()
            .filter(|node| node.kind() == SyntaxKind::TypeExpression)
            .count(),
        1
    );
    assert_eq!(
        tags[0]
            .descendants()
            .filter(|node| node.kind() == SyntaxKind::PolymorphicVariantPayload)
            .count(),
        1
    );
    assert!(
        !tags[0]
            .descendants()
            .any(|node| node.kind() == SyntaxKind::Missing)
    );

    let (green, exit) = run_type(":{@ A}");
    assert_eq!(green.to_string(), ":{@ A}");
    assert!(matches!(exit, Some(Err(Either::Right(_)))));
    let variant = polymorphic_variant_node(green);
    let tag = variant
        .children()
        .find(|node| node.kind() == SyntaxKind::PolymorphicVariantTag)
        .expect("recovered tag");
    let error = tag
        .children()
        .find(|node| node.kind() == SyntaxKind::Error)
        .expect("malformed tag error");
    assert_eq!(error.text().to_string(), "@");
    assert!(
        tag.children_with_tokens()
            .filter_map(|element| element.into_token())
            .any(|token| token.kind() == SyntaxKind::Whitespace && token.text() == " ")
    );

    let (green, exit) = run_type(":{@ ,B}");
    assert_eq!(green.to_string(), ":{@ ,B}");
    assert!(matches!(exit, Some(Err(Either::Right(_)))));
    let variant = polymorphic_variant_node(green);
    assert!(
        variant
            .children_with_tokens()
            .filter_map(|element| element.into_token())
            .any(|token| token.kind() == SyntaxKind::Whitespace && token.text() == " ")
    );
    assert_eq!(
        variant
            .descendants()
            .filter(|node| node.kind() == SyntaxKind::Error)
            .map(|node| node.text().to_string())
            .collect::<Vec<_>>(),
        ["@"]
    );

    let (green, exit) = run_type(":{@\n B}");
    assert_eq!(green.to_string(), ":{@\n B");
    assert!(matches!(
        exit,
        Some(Err(Either::Left(item)))
            if matches!(item.payload, Payload::Token(ref token) if token.kind == TokenKind::RBrace)
    ));
    let top = top_type_expression(&green);
    let variant = top
        .descendants()
        .find(|node| node.kind() == SyntaxKind::PolymorphicVariantType)
        .expect("polymorphic variant type");
    assert_eq!(variant.text().to_string(), ":{@");
    assert_eq!(
        variant
            .descendants()
            .filter(|node| node.kind() == SyntaxKind::Error)
            .map(|node| node.text().to_string())
            .collect::<Vec<_>>(),
        ["@"]
    );
    assert_eq!(
        variant
            .descendants()
            .filter(|node| node.kind() == SyntaxKind::Missing)
            .count(),
        1
    );
    assert!(
        top.children()
            .any(|node| node.kind() == SyntaxKind::TypeApplyArgument)
    );

    let (green, exit) = run_type(":{@;A}");
    assert_eq!(green.to_string(), ":{@;A}");
    assert!(matches!(exit, Some(Err(Either::Right(_)))));
    let variant = polymorphic_variant_node(green);
    assert_eq!(
        variant
            .descendants()
            .filter(|node| node.kind() == SyntaxKind::Error)
            .map(|node| node.text().to_string())
            .collect::<Vec<_>>(),
        ["@", ";"]
    );

    let (green, exit) = run_type("F(:{@; B)");
    assert_eq!(green.to_string(), "F(:{@; B)");
    assert!(matches!(exit, Some(Err(Either::Right(_)))));
    let root = SyntaxNode::new_root(green);
    let variant = root
        .descendants()
        .find(|node| node.kind() == SyntaxKind::PolymorphicVariantType)
        .expect("polymorphic variant type");
    assert_eq!(variant.text().to_string(), ":{@");
    assert_eq!(
        variant
            .descendants()
            .filter(|node| node.kind() == SyntaxKind::Error)
            .map(|node| node.text().to_string())
            .collect::<Vec<_>>(),
        ["@"]
    );
    let call = root
        .descendants()
        .find(|node| node.kind() == SyntaxKind::TypeCallTail)
        .expect("outer call");
    assert!(
        call.children_with_tokens()
            .filter_map(|element| element.into_token())
            .any(|token| token.kind() == SyntaxKind::Semicolon)
    );

    let (green, exit) = run_type("(:{@ )");
    assert_eq!(green.to_string(), "(:{@ )");
    assert!(matches!(exit, Some(Err(Either::Right(_)))));
    let root = SyntaxNode::new_root(green);
    let variant = root
        .descendants()
        .find(|node| node.kind() == SyntaxKind::PolymorphicVariantType)
        .expect("polymorphic variant type");
    assert_eq!(variant.text().to_string(), ":{@");
    let group = root
        .descendants()
        .find(|node| node.kind() == SyntaxKind::ParenthesizedTypeGroup)
        .expect("outer group");
    assert!(
        group
            .children_with_tokens()
            .filter_map(|element| element.into_token())
            .any(|token| token.kind() == SyntaxKind::Whitespace && token.text() == " ")
    );
}

#[test]
fn polymorphic_variant_type_recovers_payload_boundaries_and_malformed_runs() {
    fn polymorphic_variant_node(green: GreenNode) -> SyntaxNode {
        SyntaxNode::new_root(green)
            .descendants()
            .find(|node| node.kind() == SyntaxKind::PolymorphicVariantType)
            .expect("polymorphic variant type")
    }

    fn only_payload(variant: &SyntaxNode) -> SyntaxNode {
        let tag = variant
            .children()
            .find(|node| node.kind() == SyntaxKind::PolymorphicVariantTag)
            .expect("polymorphic variant tag");
        tag.children()
            .find(|node| node.kind() == SyntaxKind::PolymorphicVariantPayload)
            .expect("polymorphic variant payload")
    }

    let (green, exit) = run_type(":{A(Int)}");
    assert_eq!(green.to_string(), ":{A(Int)}");
    assert!(matches!(exit, Some(Err(Either::Right(_)))));
    let variant = polymorphic_variant_node(green);
    let payload = only_payload(&variant);
    assert_eq!(
        payload
            .children()
            .map(|node| node.kind())
            .collect::<Vec<_>>(),
        [SyntaxKind::Missing, SyntaxKind::TypeExpression]
    );

    for (source, error_text) in [
        (":{A @Int}", "@"),
        (":{A @ Int}", "@"),
        (":{A @@Int}", "@@"),
    ] {
        let (green, exit) = run_type(source);
        assert_eq!(green.to_string(), source, "{source:?}");
        assert!(matches!(exit, Some(Err(Either::Right(_)))), "{source:?}");
        let variant = polymorphic_variant_node(green);
        let payload = only_payload(&variant);
        let error = payload
            .children()
            .find(|node| node.kind() == SyntaxKind::Error)
            .expect("malformed payload error");
        assert_eq!(error.text().to_string(), error_text, "{source:?}");
        assert_eq!(
            error.parent().map(|node| node.kind()),
            Some(SyntaxKind::PolymorphicVariantPayload),
            "{source:?}"
        );
        assert_eq!(
            payload
                .children()
                .filter(|node| node.kind() == SyntaxKind::TypeExpression)
                .count(),
            1,
            "{source:?}"
        );
        assert!(
            !variant
                .descendants()
                .any(|node| node.kind() == SyntaxKind::Missing),
            "{source:?}"
        );
    }

    let (green, exit) = run_type(":{A @ Int}");
    assert_eq!(green.to_string(), ":{A @ Int}");
    assert!(matches!(exit, Some(Err(Either::Right(_)))));
    let payload = only_payload(&polymorphic_variant_node(green));
    assert!(
        payload
            .children_with_tokens()
            .filter_map(|element| element.into_token())
            .any(|token| token.kind() == SyntaxKind::Whitespace && token.text() == " ")
    );

    for source in [":{A @}", ":{A @,B}", ":{A @;B}", ":{A @]}"] {
        let (green, exit) = run_type(source);
        assert_eq!(green.to_string(), source, "{source:?}");
        assert!(matches!(exit, Some(Err(Either::Right(_)))), "{source:?}");
        let variant = polymorphic_variant_node(green);
        let payload = only_payload(&variant);
        assert_eq!(
            payload
                .children()
                .filter(|node| node.kind() == SyntaxKind::Error)
                .map(|node| node.text().to_string())
                .collect::<Vec<_>>(),
            ["@"],
            "{source:?}"
        );
        assert!(
            !payload
                .children()
                .any(|node| node.kind() == SyntaxKind::Missing),
            "{source:?}"
        );
    }

    let (green, exit) = run_type(":{A @,B}");
    assert_eq!(green.to_string(), ":{A @,B}");
    assert!(matches!(exit, Some(Err(Either::Right(_)))));
    let variant = polymorphic_variant_node(green);
    assert_eq!(
        variant
            .children()
            .filter(|node| node.kind() == SyntaxKind::PolymorphicVariantTag)
            .count(),
        2
    );
    assert!(
        variant
            .children_with_tokens()
            .filter_map(|element| element.into_token())
            .any(|token| token.kind() == SyntaxKind::Comma)
    );

    for (source, separator) in [(":{A @ }", None), (":{A @ ;B}", Some(";"))] {
        let (green, exit) = run_type(source);
        assert_eq!(green.to_string(), source, "{source:?}");
        assert!(matches!(exit, Some(Err(Either::Right(_)))), "{source:?}");
        let variant = polymorphic_variant_node(green);
        let payload = only_payload(&variant);
        assert_eq!(payload.text().to_string(), " @", "{source:?}");
        assert_eq!(
            variant
                .children_with_tokens()
                .filter_map(|element| element.into_token())
                .filter(|token| token.kind() == SyntaxKind::Whitespace)
                .map(|token| token.text().to_string())
                .collect::<Vec<_>>(),
            [" "],
            "{source:?}"
        );
        if let Some(separator) = separator {
            let error = variant
                .children()
                .find(|node| node.kind() == SyntaxKind::Error && node.text() == separator)
                .expect("local separator error");
            assert_eq!(
                error.parent().map(|node| node.kind()),
                Some(SyntaxKind::PolymorphicVariantType),
                "{source:?}"
            );
        } else {
            assert!(
                variant
                    .children_with_tokens()
                    .filter_map(|element| element.into_token())
                    .any(|token| token.kind() == SyntaxKind::RBrace)
            );
        }
    }

    let (green, exit) = run_type(":{A @\nB}");
    assert_eq!(green.to_string(), ":{A @\nB}");
    assert!(matches!(exit, Some(Err(Either::Right(_)))));
    let variant = polymorphic_variant_node(green);
    assert_eq!(
        variant
            .children()
            .filter(|node| node.kind() == SyntaxKind::PolymorphicVariantTag)
            .count(),
        2
    );

    let (green, exit) = run_type(":{A @\n B}");
    assert_eq!(green.to_string(), ":{A @\n B");
    assert!(matches!(
        exit,
        Some(Err(Either::Left(item)))
            if matches!(item.payload, Payload::Token(ref token) if token.kind == TokenKind::RBrace)
    ));
    let top = top_type_expression(&green);
    let variant = top
        .descendants()
        .find(|node| node.kind() == SyntaxKind::PolymorphicVariantType)
        .expect("polymorphic variant type");
    assert_eq!(variant.text().to_string(), ":{A @");
    assert!(
        top.children()
            .any(|node| node.kind() == SyntaxKind::TypeApplyArgument)
    );

    for (source, boundary) in [(":{A @;B}", ";"), (":{A @]}", "]")] {
        let (green, exit) = run_type(source);
        assert_eq!(green.to_string(), source, "{source:?}");
        assert!(matches!(exit, Some(Err(Either::Right(_)))), "{source:?}");
        let variant = polymorphic_variant_node(green);
        let error = variant
            .children()
            .find(|node| node.kind() == SyntaxKind::Error && node.text() == boundary)
            .expect("local payload boundary error");
        assert_eq!(
            error.parent().map(|node| node.kind()),
            Some(SyntaxKind::PolymorphicVariantType),
            "{source:?}"
        );
    }

    let (green, exit) = run_type("F(:{A @ )");
    assert_eq!(green.to_string(), "F(:{A @ )");
    assert!(matches!(exit, Some(Err(Either::Right(_)))));
    let root = SyntaxNode::new_root(green);
    let variant = root
        .descendants()
        .find(|node| node.kind() == SyntaxKind::PolymorphicVariantType)
        .expect("polymorphic variant type");
    assert_eq!(variant.text().to_string(), ":{A @");
    let payload = only_payload(&variant);
    assert_eq!(
        payload
            .children()
            .filter(|node| node.kind() == SyntaxKind::Error)
            .map(|node| node.text().to_string())
            .collect::<Vec<_>>(),
        ["@"]
    );
    let call = root
        .descendants()
        .find(|node| node.kind() == SyntaxKind::TypeCallTail)
        .expect("outer call");
    assert!(
        call.children_with_tokens()
            .filter_map(|element| element.into_token())
            .any(|token| token.kind() == SyntaxKind::Whitespace && token.text() == " ")
    );
    assert!(
        call.children_with_tokens()
            .filter_map(|element| element.into_token())
            .any(|token| token.kind() == SyntaxKind::RParen)
    );
}

#[test]
fn polymorphic_variant_type_recovers_local_separators_and_closes() {
    for source in [":{;A}", ":{A;B}", ":{A ; B}"] {
        let (green, exit) = run_type(source);
        assert_eq!(green.to_string(), source, "{source:?}");
        assert!(matches!(exit, Some(Err(Either::Right(_)))), "{source:?}");
        let variant = SyntaxNode::new_root(green)
            .descendants()
            .find(|node| node.kind() == SyntaxKind::PolymorphicVariantType)
            .expect("polymorphic variant type");
        let error = variant
            .descendants()
            .find(|node| node.kind() == SyntaxKind::Error)
            .expect("local semicolon error");
        assert_eq!(error.text().to_string(), ";", "{source:?}");
        assert_eq!(
            error.parent().map(|node| node.kind()),
            Some(SyntaxKind::PolymorphicVariantType)
        );
    }

    for (source, missing) in [(":{]}", 0), (":{]", 1)] {
        let (green, exit) = run_type(source);
        assert_eq!(green.to_string(), source, "{source:?}");
        assert!(matches!(exit, Some(Err(Either::Right(_)))), "{source:?}");
        let variant = SyntaxNode::new_root(green)
            .descendants()
            .find(|node| node.kind() == SyntaxKind::PolymorphicVariantType)
            .expect("polymorphic variant type");
        let error = variant
            .descendants()
            .find(|node| node.kind() == SyntaxKind::Error)
            .expect("local close error");
        assert_eq!(error.text().to_string(), "]", "{source:?}");
        assert_eq!(
            variant
                .descendants()
                .filter(|node| node.kind() == SyntaxKind::Missing)
                .count(),
            missing,
            "{source:?}"
        );
    }
}

#[test]
fn polymorphic_variant_type_handoffs_outer_closes_and_separators() {
    let (green, exit) = run_type("(:{A)");
    assert_eq!(green.to_string(), "(:{A)");
    assert!(matches!(exit, Some(Err(Either::Right(_)))));
    let root = SyntaxNode::new_root(green);
    let variant = root
        .descendants()
        .find(|node| node.kind() == SyntaxKind::PolymorphicVariantType)
        .expect("polymorphic variant type");
    assert_eq!(
        variant
            .descendants()
            .filter(|node| node.kind() == SyntaxKind::Missing)
            .count(),
        1
    );
    assert!(
        !variant
            .descendants()
            .any(|node| node.kind() == SyntaxKind::Error)
    );

    for source in ["F(:{A])", "F({a: :{A)"] {
        let (green, exit) = run_type(source);
        assert_eq!(green.to_string(), source, "{source:?}");
        assert!(matches!(exit, Some(Err(Either::Right(_)))), "{source:?}");
        let root = SyntaxNode::new_root(green);
        let variant = root
            .descendants()
            .find(|node| node.kind() == SyntaxKind::PolymorphicVariantType)
            .expect("polymorphic variant type");
        assert_eq!(
            variant
                .descendants()
                .filter(|node| node.kind() == SyntaxKind::Missing)
                .count(),
            1,
            "{source:?}"
        );
        let errors = variant
            .descendants()
            .filter(|node| node.kind() == SyntaxKind::Error)
            .map(|node| node.text().to_string())
            .collect::<Vec<_>>();
        assert_eq!(
            errors,
            if source == "F(:{A])" {
                vec!["]"]
            } else {
                vec![]
            }
        );
        if source == "F({a: :{A)" {
            let record = root
                .descendants()
                .find(|node| node.kind() == SyntaxKind::NamedRecordType)
                .expect("named record type");
            assert_eq!(
                record
                    .children()
                    .filter(|node| node.kind() == SyntaxKind::Missing)
                    .count(),
                1
            );
            let call = root
                .descendants()
                .find(|node| node.kind() == SyntaxKind::TypeCallTail)
                .expect("type call tail");
            assert!(
                !call
                    .children()
                    .any(|node| node.kind() == SyntaxKind::Missing)
            );
        }
    }

    for (source, outer) in [
        ("F(:{A; B)", SyntaxKind::TypeCallTail),
        ("{a: :{A; b: B}", SyntaxKind::NamedRecordType),
    ] {
        let (green, exit) = run_type(source);
        assert_eq!(green.to_string(), source, "{source:?}");
        assert!(matches!(exit, Some(Err(Either::Right(_)))), "{source:?}");
        let root = SyntaxNode::new_root(green);
        let variant = root
            .descendants()
            .find(|node| node.kind() == SyntaxKind::PolymorphicVariantType)
            .expect("polymorphic variant type");
        assert_eq!(variant.text().to_string(), ":{A", "{source:?}");
        assert_eq!(
            variant
                .descendants()
                .filter(|node| node.kind() == SyntaxKind::Missing)
                .count(),
            1,
            "{source:?}"
        );
        assert!(
            !variant
                .descendants()
                .any(|node| node.kind() == SyntaxKind::Error)
        );
        let owner = root
            .descendants()
            .find(|node| node.kind() == outer)
            .expect("outer owner");
        assert!(owner.text().to_string().contains(';'), "{source:?}");
    }

    for (source, outer) in [
        ("F(:{A;B)", SyntaxKind::TypeCallTail),
        ("{a: :{A;b:B}", SyntaxKind::NamedRecordType),
    ] {
        let (green, exit) = run_type(source);
        assert_eq!(green.to_string(), source, "{source:?}");
        assert!(matches!(exit, Some(Err(Either::Right(_)))), "{source:?}");
        let root = SyntaxNode::new_root(green);
        let variant = root
            .descendants()
            .find(|node| node.kind() == SyntaxKind::PolymorphicVariantType)
            .expect("polymorphic variant type");
        assert_eq!(variant.text().to_string(), ":{A", "{source:?}");
        assert!(
            !variant
                .descendants_with_tokens()
                .filter_map(|element| element.into_token())
                .any(|token| token.kind() == SyntaxKind::Semicolon),
            "{source:?}"
        );
        let owner = root
            .descendants()
            .find(|node| node.kind() == outer)
            .expect("outer owner");
        assert!(
            owner
                .descendants_with_tokens()
                .filter_map(|element| element.into_token())
                .any(|token| token.kind() == SyntaxKind::Semicolon),
            "{source:?}"
        );
    }

    let (green, exit) = run_type("F(:{A ])");
    assert_eq!(green.to_string(), "F(:{A ])");
    assert!(matches!(exit, Some(Err(Either::Right(_)))));
    let root = SyntaxNode::new_root(green);
    let variant = root
        .descendants()
        .find(|node| node.kind() == SyntaxKind::PolymorphicVariantType)
        .expect("polymorphic variant type");
    let error = variant
        .children()
        .find(|node| node.kind() == SyntaxKind::Error)
        .expect("local close error");
    assert_eq!(error.text().to_string(), "]");
    assert!(
        variant
            .children_with_tokens()
            .filter_map(|element| element.into_token())
            .any(|token| token.kind() == SyntaxKind::Whitespace && token.text() == " ")
    );

    let (green, exit) = run_type("F(:{A )");
    assert_eq!(green.to_string(), "F(:{A )");
    assert!(matches!(exit, Some(Err(Either::Right(_)))));
    let root = SyntaxNode::new_root(green);
    let variant = root
        .descendants()
        .find(|node| node.kind() == SyntaxKind::PolymorphicVariantType)
        .expect("polymorphic variant type");
    assert_eq!(variant.text().to_string(), ":{A");
    let call = root
        .descendants()
        .find(|node| node.kind() == SyntaxKind::TypeCallTail)
        .expect("type call tail");
    assert!(
        call.children_with_tokens()
            .filter_map(|element| element.into_token())
            .any(|token| token.kind() == SyntaxKind::Whitespace && token.text() == " ")
    );
}

#[test]
fn polymorphic_variant_type_recovers_newline_and_eof_boundaries() {
    for (source, tags, missing) in [
        (":{A\nB}", 2, 0),
        (":{A\n}", 1, 0),
        (":{A\n", 1, 2),
        (":{", 0, 1),
        (":{A", 1, 1),
        (":{A,", 1, 2),
    ] {
        let (green, exit) = run_type(source);
        assert_eq!(green.to_string(), source, "{source:?}");
        assert!(matches!(exit, Some(Err(Either::Right(_)))), "{source:?}");
        let variant = SyntaxNode::new_root(green)
            .descendants()
            .find(|node| node.kind() == SyntaxKind::PolymorphicVariantType)
            .expect("polymorphic variant type");
        assert_eq!(
            variant
                .children()
                .filter(|node| node.kind() == SyntaxKind::PolymorphicVariantTag)
                .count(),
            tags,
            "{source:?}"
        );
        assert_eq!(
            variant
                .descendants()
                .filter(|node| node.kind() == SyntaxKind::Missing)
                .count(),
            missing,
            "{source:?}"
        );
    }

    let (green, exit) = run_type(":{A\n  B}");
    assert_eq!(green.to_string(), ":{A\n  B");
    assert!(matches!(
        exit,
        Some(Err(Either::Left(item)))
            if matches!(item.payload, Payload::Token(ref token) if token.kind == TokenKind::RBrace)
    ));
    let top = top_type_expression(&green);
    let variant = top
        .descendants()
        .find(|node| node.kind() == SyntaxKind::PolymorphicVariantType)
        .expect("polymorphic variant type");
    assert_eq!(variant.text().to_string(), ":{A");
    assert_eq!(
        variant
            .descendants()
            .filter(|node| node.kind() == SyntaxKind::Missing)
            .count(),
        1
    );
    assert!(
        top.children()
            .any(|node| node.kind() == SyntaxKind::TypeApplyArgument)
    );
}

#[test]
fn polymorphic_variant_type_composes_with_type_tails() {
    let (green, exit) = run_type("F :{A} -> Out");
    assert_eq!(green.to_string(), "F :{A} -> Out");
    assert!(matches!(exit, Some(Err(Either::Right(_)))));
    let top = top_type_expression(&green);
    assert!(
        top.children()
            .any(|node| node.kind() == SyntaxKind::TypeApplyArgument)
    );
    assert!(
        top.children()
            .any(|node| node.kind() == SyntaxKind::TypeArrowTail)
    );

    let path = run_type(":{A}::Result").0;
    assert!(
        top_type_expression(&path)
            .children()
            .any(|node| node.kind() == SyntaxKind::TypePathTail)
    );

    let (green, exit) = run_type("F:{A}");
    assert_eq!(green.to_string(), "F");
    assert!(matches!(exit, Some(Err(Either::Left(_)))));

    for source in [": {A}", ":/*comment*/{A}", ":\n{A}", ":"] {
        let (green, exit) = run_type(source);
        assert_eq!(green.to_string(), "", "{source:?}");
        assert!(exit.is_none(), "{source:?}");
    }
}

#[test]
fn bracket_rows_attach_at_leading_and_arrow_positions() {
    for (source, items) in [("[] T", 0), ("[e] T", 1), ("[e, f; g\nh] T", 4)] {
        let (green, exit) = run_type(source);
        assert_eq!(green.to_string(), source, "{source:?}");
        assert!(matches!(exit, Some(Err(Either::Right(_)))), "{source:?}");
        let top = top_type_expression(&green);
        let row = top
            .children()
            .find(|node| node.kind() == SyntaxKind::BracketRow)
            .expect("leading bracket row");
        assert_eq!(
            row.children()
                .filter(|node| node.kind() == SyntaxKind::TypeExpression)
                .count(),
            items,
            "{source:?}"
        );
    }

    let source = "T [e, f] -> U -> V";
    let (green, exit) = run_type(source);
    assert_eq!(green.to_string(), source);
    assert!(matches!(exit, Some(Err(Either::Right(_)))));
    let top = top_type_expression(&green);
    let tail = top
        .children()
        .find(|node| node.kind() == SyntaxKind::TypeArrowTail)
        .expect("bracket row arrow tail");
    assert!(
        tail.children()
            .any(|node| node.kind() == SyntaxKind::BracketRow)
    );
    assert_eq!(
        top.descendants()
            .filter(|node| node.kind() == SyntaxKind::TypeArrowTail)
            .count(),
        2
    );

    for source in ["T -> [e] U", "F([e] T)", "[[e] T] U", "[e] F [io] -> U"] {
        let (green, exit) = run_type(source);
        assert_eq!(green.to_string(), source, "{source:?}");
        assert!(matches!(exit, Some(Err(Either::Right(_)))), "{source:?}");
    }
}

#[test]
fn bracket_row_arrow_is_mandatory_at_normal_boundaries() {
    for source in ["T [e]", "T [e] U", "F(T [e])"] {
        let (green, exit) = run_type(source);
        assert_eq!(green.to_string(), source, "{source:?}");
        assert!(matches!(exit, Some(Err(Either::Right(_)))), "{source:?}");
        assert!(
            SyntaxNode::new_root(green)
                .descendants()
                .any(|node| node.kind() == SyntaxKind::Missing),
            "{source:?}"
        );
    }

    let (green, exit) = run_type("T [e]\nU");
    assert_eq!(green.to_string(), "T [e]");
    assert!(matches!(exit, Some(Err(Either::Left(_)))));
    assert!(
        SyntaxNode::new_root(green)
            .descendants()
            .any(|node| node.kind() == SyntaxKind::Missing)
    );
}

#[test]
fn leading_bracket_row_head_is_mandatory_at_normal_boundaries() {
    for source in ["[e]", "F([e])"] {
        let (green, exit) = run_type(source);
        assert_eq!(green.to_string(), source, "{source:?}");
        assert!(matches!(exit, Some(Err(Either::Right(_)))), "{source:?}");
        assert!(
            SyntaxNode::new_root(green)
                .descendants()
                .any(|node| node.kind() == SyntaxKind::Missing),
            "{source:?}"
        );
    }

    let (green, exit) = run_type("[e]\nT");
    assert_eq!(green.to_string(), "[e]");
    assert!(matches!(exit, Some(Err(Either::Left(_)))));
    assert!(
        SyntaxNode::new_root(green)
            .descendants()
            .any(|node| node.kind() == SyntaxKind::Missing)
    );
}

#[test]
fn leading_bracket_row_retries_a_balanced_second_row_as_one_error() {
    for source in ["[e][f]T", "[e][/*]*/f]T"] {
        let (green, exit) = run_type(source);
        assert_eq!(green.to_string(), source, "{source:?}");
        assert!(matches!(exit, Some(Err(Either::Right(_)))), "{source:?}");
        let top = top_type_expression(&green);
        assert_eq!(
            top.descendants()
                .filter(|node| node.kind() == SyntaxKind::BracketRow)
                .count(),
            1,
            "{source:?}"
        );
        assert_eq!(
            top.children()
                .filter(|node| node.kind() == SyntaxKind::Error)
                .count(),
            1,
            "{source:?}"
        );
    }

    let (green, exit) = run_type("[e][f");
    assert_eq!(green.to_string(), "[e]");
    assert!(matches!(exit, Some(Err(Either::Left(_)))));
    assert!(
        !SyntaxNode::new_root(green)
            .descendants()
            .any(|node| node.kind() == SyntaxKind::Error)
    );
}

#[test]
fn leading_bracket_row_retries_malformed_heads_without_a_missing_cascade() {
    for source in ["[e] @ T", "[e] @"] {
        let (green, exit) = run_type(source);
        assert_eq!(green.to_string(), source, "{source:?}");
        assert!(matches!(exit, Some(Err(Either::Right(_)))), "{source:?}");
        let top = top_type_expression(&green);
        assert_eq!(
            top.children()
                .filter(|node| node.kind() == SyntaxKind::Error)
                .count(),
            1,
            "{source:?}"
        );
        assert!(
            !top.children()
                .any(|node| node.kind() == SyntaxKind::Missing),
            "{source:?}"
        );
        assert!(
            top.descendants_with_tokens()
                .filter_map(|element| element.into_token())
                .filter(|token| token.kind() == SyntaxKind::Whitespace)
                .all(|token| token
                    .parent()
                    .is_some_and(|parent| parent.kind() == SyntaxKind::TypeExpression)),
            "{source:?}"
        );
    }

    let (green, exit) = run_type("[e] @\nT");
    assert_eq!(green.to_string(), "[e] @");
    assert!(matches!(exit, Some(Err(Either::Left(_)))));
    assert!(
        !top_type_expression(&green)
            .children()
            .any(|node| node.kind() == SyntaxKind::Missing)
    );
}

#[test]
fn bracket_rows_recover_malformed_items_and_local_closes() {
    for (source, missing) in [
        ("T [)] -> U", 1),
        ("T [e)] -> U", 0),
        ("T [@ A] -> U", 0),
        ("T [@] -> U", 0),
        ("T [@", 2),
        ("T [e)", 2),
        ("T [@, A] -> U", 0),
        ("T [e @ A] -> U", 0),
    ] {
        let (green, exit) = run_type(source);
        assert_eq!(green.to_string(), source, "{source:?}");
        assert!(matches!(exit, Some(Err(Either::Right(_)))), "{source:?}");
        let root = SyntaxNode::new_root(green);
        assert_eq!(
            root.descendants()
                .filter(|node| node.kind() == SyntaxKind::Error)
                .count(),
            1,
            "{source:?}"
        );
        assert_eq!(
            root.descendants()
                .filter(|node| node.kind() == SyntaxKind::Missing)
                .count(),
            missing,
            "{source:?}"
        );
    }

    let (green, exit) = run_type("T [@ A] -> U");
    assert!(matches!(exit, Some(Err(Either::Right(_)))));
    let error = SyntaxNode::new_root(green)
        .descendants()
        .find(|node| node.kind() == SyntaxKind::Error)
        .expect("bracket item error");
    assert_eq!(error.text().to_string(), "@ ");

    let (green, exit) = run_type("[e");
    assert_eq!(green.to_string(), "[e");
    assert!(matches!(exit, Some(Err(Either::Right(_)))));
    assert_eq!(
        SyntaxNode::new_root(green)
            .descendants()
            .filter(|node| node.kind() == SyntaxKind::Missing)
            .count(),
        2
    );

    let (green, exit) = run_type("T [e\n  @]");
    assert_eq!(green.to_string(), "T [e");
    assert!(matches!(exit, Some(Err(Either::Left(_)))));
    let root = SyntaxNode::new_root(green);
    assert!(
        !root
            .descendants()
            .any(|node| node.kind() == SyntaxKind::Error)
    );
    assert_eq!(
        root.descendants()
            .filter(|node| node.kind() == SyntaxKind::Missing)
            .count(),
        1
    );
}

#[test]
fn bracket_row_recovery_keeps_item_and_close_slots_distinct() {
    for (source, error_text, missing) in [
        ("T [:] -> U", ":", 0),
        ("T [@\nA] -> U", "@", 0),
        ("T [@\n  A] -> U", "@\n  ", 0),
        ("T [A\n  )] -> U", ")", 0),
        ("T [@/* comment */A] -> U", "@/* comment */", 0),
        ("T [@/*\n*/A] -> U", "@/*\n*/", 0),
    ] {
        let (green, exit) = run_type(source);
        assert_eq!(green.to_string(), source, "{source:?}");
        assert!(matches!(exit, Some(Err(Either::Right(_)))), "{source:?}");
        let root = SyntaxNode::new_root(green);
        let errors = root
            .descendants()
            .filter(|node| node.kind() == SyntaxKind::Error)
            .collect::<Vec<_>>();
        assert_eq!(errors.len(), 1, "{source:?}");
        assert_eq!(errors[0].text().to_string(), error_text, "{source:?}");
        assert_eq!(
            root.descendants()
                .filter(|node| node.kind() == SyntaxKind::Missing)
                .count(),
            missing,
            "{source:?}"
        );
    }

    let (green, exit) = run_type("T [A\n  ] -> U");
    assert_eq!(green.to_string(), "T [A\n  ] -> U");
    assert!(matches!(exit, Some(Err(Either::Right(_)))));
    let root = SyntaxNode::new_root(green);
    assert!(
        !root
            .descendants()
            .any(|node| matches!(node.kind(), SyntaxKind::Error | SyntaxKind::Missing))
    );

    let (green, exit) = run_type("T [");
    assert_eq!(green.to_string(), "T [");
    assert!(matches!(exit, Some(Err(Either::Right(_)))));
    assert_eq!(
        SyntaxNode::new_root(green)
            .descendants()
            .filter(|node| node.kind() == SyntaxKind::Missing)
            .count(),
        3
    );

    for (source, errors, missing) in [
        ("T [e,)] -> U", 1, 1),
        ("T [@,)] -> U", 2, 1),
        ("T [e))] -> U", 2, 0),
        ("T [e))", 2, 2),
        ("T [)", 1, 3),
    ] {
        let (green, exit) = run_type(source);
        assert_eq!(green.to_string(), source, "{source:?}");
        assert!(matches!(exit, Some(Err(Either::Right(_)))), "{source:?}");
        let root = SyntaxNode::new_root(green);
        assert_eq!(
            root.descendants()
                .filter(|node| node.kind() == SyntaxKind::Error)
                .count(),
            errors,
            "{source:?}"
        );
        assert_eq!(
            root.descendants()
                .filter(|node| node.kind() == SyntaxKind::Missing)
                .count(),
            missing,
            "{source:?}"
        );
    }

    for (source, parsed) in [("T [e) U]", "T [e)"), ("T [e)\nU]", "T [e)")] {
        let (green, exit) = run_type(source);
        assert_eq!(green.to_string(), parsed, "{source:?}");
        assert!(matches!(exit, Some(Err(Either::Left(_)))), "{source:?}");
        let root = SyntaxNode::new_root(green);
        assert_eq!(
            root.descendants()
                .filter(|node| node.kind() == SyntaxKind::Error)
                .count(),
            1,
            "{source:?}"
        );
        assert_eq!(
            root.descendants()
                .filter(|node| node.kind() == SyntaxKind::Missing)
                .count(),
            1,
            "{source:?}"
        );
    }

    let (green, exit) = run_type("T [e)\n");
    assert_eq!(green.to_string(), "T [e)\n");
    assert!(matches!(exit, Some(Err(Either::Right(_)))));
    let root = SyntaxNode::new_root(green);
    let newline = root
        .descendants_with_tokens()
        .filter_map(|element| element.into_token())
        .find(|token| token.kind() == SyntaxKind::Newline)
        .expect("caller newline");
    assert_ne!(
        newline.parent().expect("newline parent").kind(),
        SyntaxKind::BracketRow
    );
    assert_eq!(
        root.descendants()
            .filter(|node| node.kind() == SyntaxKind::Error)
            .count(),
        1
    );
    assert_eq!(
        root.descendants()
            .filter(|node| node.kind() == SyntaxKind::Missing)
            .count(),
        2
    );
}
