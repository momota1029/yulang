use crate::tests::recovery_output::recovery_groups;
use crate::{
    OperatorTable, SyntaxNode,
    recovery_record::{GrammarRole, StatementRole},
    syntax_kind::SyntaxKind,
};
use crate::{header::discover_header, source_file::parse_root_candidate};

#[test]
fn root_binding_intro_wins_over_header_words() {
    for word in ["use", "lazy", "prefix", "infix", "suffix", "nullfix"] {
        let source = format!("my {word} = 値\r\nuse later");
        let header = discover_header(&source);
        assert_eq!(header.coverage, 0..0);
        assert!(header.imports.is_empty());
        assert!(header.operators.is_empty());
        assert!(header.recoveries.is_empty());
        let root = parse_root_candidate(&source, &OperatorTable::empty(), &header.recoveries);
        assert_eq!(root.green.to_string(), source);
        assert!(
            root.committed_recoveries.is_empty(),
            "{word}: {:?}",
            root.committed_recoveries
        );
        let syntax = SyntaxNode::new_root(root.green);
        assert_eq!(
            syntax
                .children()
                .map(|node| node.kind())
                .collect::<Vec<_>>(),
            [SyntaxKind::BindingStatement, SyntaxKind::UseDeclaration]
        );
    }
}

#[test]
fn root_initial_indent_is_rejected_but_semicolon_gap_is_allowed() {
    for source in ["  use a", "\n  my a = 1"] {
        let root = parse_root_candidate(source, &OperatorTable::empty(), &[]);
        assert_eq!(root.green.to_string(), source);
        assert_eq!(root.committed_recoveries.len(), 1);
        assert_eq!(
            root.committed_recoveries[0].site.role,
            GrammarRole::Statement(StatementRole::Starter)
        );
        let syntax = SyntaxNode::new_root(root.green);
        assert_eq!(syntax.children().count(), 0);
        let groups = recovery_groups(&syntax);
        assert_eq!(groups.len(), 1);
        assert_eq!(groups[0].parent(), Some(syntax.clone()));
        assert_eq!(groups[0].text(), source.trim_start());
    }
    let source = "a;  use b;  my c = 1";
    let root = parse_root_candidate(source, &OperatorTable::empty(), &[]);
    assert_eq!(root.green.to_string(), source);
    assert!(root.committed_recoveries.is_empty());
    let syntax = SyntaxNode::new_root(root.green);
    assert_eq!(
        syntax
            .children()
            .map(|node| node.kind())
            .collect::<Vec<_>>(),
        [
            SyntaxKind::OperatorChain,
            SyntaxKind::UseDeclaration,
            SyntaxKind::BindingStatement
        ]
    );
}

#[test]
fn root_keeps_private_and_public_lazy_operator_modifiers() {
    for source in [
        "my prefix (?) 70 = 値\r\nuse next",
        "pub lazy infix (<+>) 50 51 = 値\r\nuse next",
    ] {
        let header = discover_header(source);
        assert_eq!(header.operators.len(), 1);
        assert_eq!(header.imports.len(), 1);
        assert!(header.recoveries.is_empty());
        let root = parse_root_candidate(source, &OperatorTable::empty(), &header.recoveries);
        assert_eq!(root.green.to_string(), source);
        assert!(
            root.committed_recoveries.is_empty(),
            "{:?}",
            root.committed_recoveries
        );
        let syntax = SyntaxNode::new_root(root.green);
        assert_eq!(
            syntax
                .children()
                .map(|node| node.kind())
                .collect::<Vec<_>>(),
            [
                SyntaxKind::OperatorHeader,
                SyntaxKind::OperatorChain,
                SyntaxKind::UseDeclaration
            ]
        );
    }
}

#[test]
fn root_keeps_multiple_statements_and_separators_lossless() {
    for source in [
        "",
        " \r\n",
        "a\nb\n",
        "a;b;",
        "my a = 1\r\nmy b = 2\r\n",
        "use a\nuse b\nmy x = 1\n",
    ] {
        let header = discover_header(source);
        let root = parse_root_candidate(source, &OperatorTable::empty(), &header.recoveries);
        assert_eq!(root.green.to_string(), source, "{source:?}");
        assert!(
            root.committed_recoveries.is_empty(),
            "{source:?}: {:?}",
            root.committed_recoveries
        );
    }
}

#[test]
fn root_reconciles_header_records_after_full_only_operator_body_record() {
    let source = "prefix (?) 70 =\nuse a as\nuse good\nmy x = 1\n";
    let header = discover_header(source);
    assert!(!header.recoveries.is_empty());
    let root = parse_root_candidate(source, &OperatorTable::empty(), &header.recoveries);
    assert_eq!(root.green.to_string(), source);
    for frozen in &header.recoveries {
        assert_eq!(
            root.committed_recoveries
                .iter()
                .find(|record| record.id == frozen.id),
            Some(frozen)
        );
    }
    assert!(
        root.committed_recoveries
            .iter()
            .any(|record| record.site.role
                == GrammarRole::Statement(StatementRole::OperatorDefinitionBody))
    );
}

#[test]
fn root_error_keeps_nested_delimiters_and_literal_newlines_inside_one_run() {
    for source in [
        "] (a;\nb)\nuse good\n",
        "] [a) ;\nb]\nuse good\n",
        "] \"a;\nb\"\nuse good\n",
        "] \"\"\"a\n\"\"\"\"\nb\"\"\"\nuse good\n",
        "] ~\"a;\nb\"\nuse good\n",
        "] '[a;\nb]\nuse good\n",
        "] '{\n```text\n}\n```\n}\nuse good\n",
    ] {
        let root = parse_root_candidate(source, &OperatorTable::empty(), &[]);
        assert_eq!(root.green.to_string(), source, "{source:?}");
        assert_eq!(
            root.committed_recoveries.len(),
            1,
            "{source:?}: {:?}",
            root.committed_recoveries
        );
        assert_eq!(
            root.committed_recoveries[0].site.range,
            0..source.find("\nuse good").unwrap()
        );
        let syntax = SyntaxNode::new_root(root.green);
        assert_eq!(
            syntax
                .descendants()
                .filter(|node| node.kind() == SyntaxKind::UseDeclaration)
                .count(),
            1
        );
    }
}

#[test]
fn root_raw_error_repeats_across_a_native_semicolon_and_progresses() {
    let source = "];]\r\nnext";
    let root = parse_root_candidate(source, &OperatorTable::empty(), &[]);
    assert_eq!(root.green.to_string(), source);
    let syntax = SyntaxNode::new_root(root.green);
    let groups = recovery_groups(&syntax);
    assert_eq!(groups.len(), 2);
    assert_eq!(
        groups
            .iter()
            .map(|group| {
                (
                    usize::from(group.text_range().start())..usize::from(group.text_range().end()),
                    group.text(),
                    group.parent(),
                )
            })
            .collect::<Vec<_>>(),
        [
            (0..1, "]".into(), Some(syntax.clone())),
            (2..3, "]".into(), Some(syntax.clone()))
        ]
    );
    let direct = syntax
        .children_with_tokens()
        .map(|element| {
            (
                element.kind(),
                usize::from(element.text_range().start())..usize::from(element.text_range().end()),
                element.to_string(),
            )
        })
        .collect::<Vec<_>>();
    assert_eq!(
        direct,
        [
            (SyntaxKind::Error, 0..1, "]".into()),
            (SyntaxKind::Semicolon, 1..2, ";".into()),
            (SyntaxKind::Error, 2..3, "]".into()),
            (SyntaxKind::Newline, 3..5, "\r\n".into()),
            (SyntaxKind::OperatorChain, 5..9, "next".into()),
        ]
    );
    assert!(
        syntax
            .descendants()
            .all(|node| node.kind() != SyntaxKind::Invalid)
    );
}

#[test]
fn root_raw_error_retry_and_terminal_leading_preserve_direct_ownership() {
    use crate::recovery_record::{
        ExpectationSources, ExpectedSyntax, KeywordEvidence, RecoveryKind, RootUnexpected,
        UnexpectedSyntax,
    };

    const ROOT_KEYWORDS: [KeywordEvidence; 6] = [
        KeywordEvidence::Use,
        KeywordEvidence::Lazy,
        KeywordEvidence::Prefix,
        KeywordEvidence::Infix,
        KeywordEvidence::Suffix,
        KeywordEvidence::Nullfix,
    ];

    struct Row {
        source: &'static str,
        error_range: std::ops::Range<usize>,
        direct: Vec<(SyntaxKind, std::ops::Range<usize>, &'static str)>,
    }

    let rows = [
        Row {
            source: "];next",
            error_range: 0..1,
            direct: vec![
                (SyntaxKind::Error, 0..1, "]"),
                (SyntaxKind::Semicolon, 1..2, ";"),
                (SyntaxKind::OperatorChain, 2..6, "next"),
            ],
        },
        Row {
            source: "]\r\nnext",
            error_range: 0..1,
            direct: vec![
                (SyntaxKind::Error, 0..1, "]"),
                (SyntaxKind::Newline, 1..3, "\r\n"),
                (SyntaxKind::OperatorChain, 3..7, "next"),
            ],
        },
        Row {
            source: "] next",
            error_range: 0..6,
            direct: vec![
                (SyntaxKind::Error, 0..1, "]"),
                (SyntaxKind::Error, 1..2, " "),
                (SyntaxKind::Error, 2..6, "next"),
            ],
        },
        Row {
            source: "]\n  next",
            error_range: 0..8,
            direct: vec![
                (SyntaxKind::Error, 0..1, "]"),
                (SyntaxKind::Error, 1..2, "\n"),
                (SyntaxKind::Error, 2..4, "  "),
                (SyntaxKind::Error, 4..8, "next"),
            ],
        },
        Row {
            source: "]\r\n",
            error_range: 0..1,
            direct: vec![
                (SyntaxKind::Error, 0..1, "]"),
                (SyntaxKind::Newline, 1..3, "\r\n"),
            ],
        },
    ];

    for row in rows {
        let root = parse_root_candidate(row.source, &OperatorTable::empty(), &[]);
        assert_eq!(root.green.to_string(), row.source, "{:?}", row.source);
        assert_eq!(root.committed_recoveries.len(), 1, "{:?}", row.source);
        let record = &root.committed_recoveries[0];
        assert_eq!(record.kind, RecoveryKind::Error, "{:?}", row.source);
        assert_eq!(
            record.site.role,
            GrammarRole::Statement(StatementRole::Starter),
            "{:?}",
            row.source
        );
        assert_eq!(record.site.range, row.error_range, "{:?}", row.source);
        assert!(
            matches!(
                record.unexpected.as_ref(),
                [UnexpectedSyntax::Root(RootUnexpected::UnrecognizedStarter { range, .. })]
                    if range == &record.site.range
            ),
            "{:?}: {:?}",
            row.source,
            record.unexpected
        );
        assert_eq!(record.primary_expectation, 0, "{:?}", row.source);
        assert_eq!(
            record.expectations.len(),
            ROOT_KEYWORDS.len(),
            "{:?}",
            row.source
        );
        for (expectation, keyword) in record.expectations.iter().zip(ROOT_KEYWORDS) {
            assert_eq!(expectation.role, record.site.role, "{:?}", row.source);
            assert_eq!(
                expectation.expected,
                ExpectedSyntax::Keyword(keyword),
                "{:?}",
                row.source
            );
            assert_eq!(expectation.range, record.site.range, "{:?}", row.source);
            assert_eq!(
                expectation.sources,
                ExpectationSources::COMMITTED_RECOVERY_RULE,
                "{:?}",
                row.source
            );
        }

        let syntax = SyntaxNode::new_root(root.green);
        let groups = recovery_groups(&syntax);
        assert_eq!(groups.len(), 1, "{:?}: {groups:#?}", row.source);
        assert_eq!(groups[0].parent(), Some(syntax.clone()), "{:?}", row.source);
        assert_eq!(
            usize::from(groups[0].text_range().start())..usize::from(groups[0].text_range().end()),
            record.site.range,
            "{:?}",
            row.source
        );
        let direct = syntax
            .children_with_tokens()
            .map(|element| {
                (
                    element.kind(),
                    usize::from(element.text_range().start())
                        ..usize::from(element.text_range().end()),
                    element.to_string(),
                )
            })
            .collect::<Vec<_>>();
        assert_eq!(
            direct,
            row.direct
                .into_iter()
                .map(|(kind, range, text)| (kind, range, text.into()))
                .collect::<Vec<_>>(),
            "{:?}",
            row.source
        );
        assert!(
            syntax
                .descendants()
                .all(|node| node.kind() != SyntaxKind::Invalid),
            "{:?}: {syntax:#?}",
            row.source
        );
    }
}

#[test]
fn root_raw_error_opaque_utf8_fragments_preserve_byte_ranges() {
    let source = "] \"é;\n💥\"\nuse good\n";
    let root = parse_root_candidate(source, &OperatorTable::empty(), &[]);
    assert_eq!(root.green.to_string(), source);
    let syntax = SyntaxNode::new_root(root.green);
    let errors = syntax
        .children_with_tokens()
        .filter_map(|element| element.into_token())
        .filter(|token| token.kind() == SyntaxKind::Error)
        .map(|token| {
            (
                usize::from(token.text_range().start())..usize::from(token.text_range().end()),
                token.text().to_owned(),
            )
        })
        .collect::<Vec<_>>();
    assert_eq!(
        errors,
        [
            (0..1, "]".into()),
            (1..2, " ".into()),
            (2..3, "\"".into()),
            (3..12, "é;\n💥\"".into()),
        ]
    );
    assert_eq!(
        errors.last().unwrap().0.end,
        source.find("\nuse good").unwrap()
    );
    assert!(
        syntax
            .descendants()
            .all(|node| node.kind() != SyntaxKind::Invalid)
    );
    assert_eq!(
        syntax
            .children()
            .filter(|node| node.kind() == SyntaxKind::UseDeclaration)
            .map(|node| node.text().to_string())
            .collect::<Vec<_>>(),
        ["use good"]
    );
}

#[test]
fn root_operator_body_uses_expression_and_preserves_following_statement() {
    let source = "prefix (?) 70 = value\nmy next = 2\n";
    let header = discover_header(source);
    let root = parse_root_candidate(source, &OperatorTable::empty(), &header.recoveries);
    assert_eq!(root.green.to_string(), source);
    assert!(
        root.committed_recoveries.is_empty(),
        "{:?}",
        root.committed_recoveries
    );
    let syntax = SyntaxNode::new_root(root.green);
    assert_eq!(
        syntax
            .children()
            .map(|node| node.kind())
            .collect::<Vec<_>>(),
        [
            SyntaxKind::OperatorHeader,
            SyntaxKind::OperatorChain,
            SyntaxKind::BindingStatement
        ]
    );
    assert_eq!(
        syntax
            .descendants()
            .filter(|node| node.kind() == SyntaxKind::OperatorHeader)
            .count(),
        1
    );
}

#[test]
fn root_expression_trailing_input_has_separator_role_and_root_owned_gaps() {
    use crate::recovery_record::{ExpectedSyntax, RecoveryKind};
    let source = "値  ] \r\nnext";
    let root = parse_root_candidate(source, &OperatorTable::empty(), &[]);
    assert_eq!(root.green.to_string(), source);
    assert_eq!(root.committed_recoveries.len(), 1);
    let record = &root.committed_recoveries[0];
    assert_eq!(
        record.site.role,
        GrammarRole::Statement(StatementRole::Separator)
    );
    assert_eq!(record.kind, RecoveryKind::Error);
    assert_eq!(record.site.range, 5..6);
    assert_eq!(
        record.expectations[0].expected,
        ExpectedSyntax::StatementSeparator
    );
    let syntax = SyntaxNode::new_root(root.green);
    let children = syntax
        .children_with_tokens()
        .map(|element| (element.kind(), element.to_string()))
        .collect::<Vec<_>>();
    assert_eq!(
        children,
        [
            (SyntaxKind::OperatorChain, "値".into()),
            (SyntaxKind::Whitespace, "  ".into()),
            (SyntaxKind::Error, "]".into()),
            (SyntaxKind::Whitespace, " ".into()),
            (SyntaxKind::Newline, "\r\n".into()),
            (SyntaxKind::OperatorChain, "next".into()),
        ]
    );
}

#[test]
fn root_error_keeps_undeclared_operator_as_raw_token() {
    use crate::recovery_record::{
        RecoveryKind, RootUnexpected, RootUnexpectedHead, StatementKind, UnexpectedSyntax,
    };

    let source = "use a <+>\r\nnext";
    let root = parse_root_candidate(source, &OperatorTable::empty(), &[]);
    assert_eq!(root.green.to_string(), source);
    assert_eq!(root.committed_recoveries.len(), 1);
    let record = &root.committed_recoveries[0];
    assert_eq!(record.kind, RecoveryKind::Error);
    assert_eq!(
        record.site.role,
        GrammarRole::Statement(StatementRole::TrailingInput {
            owner: StatementKind::UseDeclaration,
        })
    );
    assert_eq!(record.site.range, 6..9);
    assert_eq!(
        record.unexpected.as_ref(),
        [UnexpectedSyntax::Root(RootUnexpected::TrailingInput {
            owner: StatementKind::UseDeclaration,
            range: 6..9,
            head: RootUnexpectedHead::OperatorLike,
        })]
    );
    let syntax = SyntaxNode::new_root(root.green);
    let error = recovery_groups(&syntax).into_iter().next().unwrap();
    assert_eq!(error.parent(), Some(syntax));
    assert_eq!(error.to_string(), "<+>");
    assert!(
        error
            .children_with_tokens()
            .any(|element| { element.kind() == SyntaxKind::Error && element.to_string() == "<+>" }),
        "{error:#?}"
    );
}

#[test]
fn root_direct_raw_error_requires_ordered_context() {
    use crate::recovery_record::{ExpectedSyntax, KeywordEvidence, RecoveryKind, StatementKind};

    const ROOT_EXPECTATIONS: &[ExpectedSyntax] = &[
        ExpectedSyntax::Keyword(KeywordEvidence::Use),
        ExpectedSyntax::Keyword(KeywordEvidence::Lazy),
        ExpectedSyntax::Keyword(KeywordEvidence::Prefix),
        ExpectedSyntax::Keyword(KeywordEvidence::Infix),
        ExpectedSyntax::Keyword(KeywordEvidence::Suffix),
        ExpectedSyntax::Keyword(KeywordEvidence::Nullfix),
    ];
    const SEPARATOR_EXPECTATIONS: &[ExpectedSyntax] = &[ExpectedSyntax::StatementSeparator];
    const BODY_EXPECTATIONS: &[ExpectedSyntax] = &[ExpectedSyntax::Expression];

    struct Row {
        prefix: &'static str,
        before_error: &'static str,
        malformed: &'static str,
        after_error: &'static str,
        role: GrammarRole,
        expectations: &'static [ExpectedSyntax],
        before_group: Vec<SyntaxKind>,
        after_group: Vec<(SyntaxKind, &'static str)>,
    }

    let trailing = |owner, accepted_owner| Row {
        prefix: "",
        before_error: " ",
        malformed: "]",
        after_error: "",
        role: GrammarRole::Statement(StatementRole::TrailingInput { owner }),
        expectations: ROOT_EXPECTATIONS,
        before_group: if owner == StatementKind::OperatorDefinition {
            vec![SyntaxKind::OperatorHeader, SyntaxKind::OperatorChain]
        } else {
            vec![accepted_owner]
        },
        after_group: vec![(SyntaxKind::OperatorChain, "next")],
    };

    let mut rows = vec![
        Row {
            prefix: "",
            before_error: "",
            malformed: "]",
            after_error: "",
            role: GrammarRole::Statement(StatementRole::Starter),
            expectations: ROOT_EXPECTATIONS,
            before_group: vec![],
            after_group: vec![(SyntaxKind::OperatorChain, "next")],
        },
        Row {
            prefix: "abc",
            before_error: "   ",
            malformed: "]",
            after_error: "",
            role: GrammarRole::Statement(StatementRole::Separator),
            expectations: SEPARATOR_EXPECTATIONS,
            before_group: vec![SyntaxKind::OperatorChain],
            after_group: vec![(SyntaxKind::OperatorChain, "next")],
        },
    ];
    for (prefix, owner, accepted_owner) in [
        (
            "use a",
            StatementKind::UseDeclaration,
            SyntaxKind::UseDeclaration,
        ),
        (
            "my x = value",
            StatementKind::BindingDeclaration,
            SyntaxKind::BindingStatement,
        ),
        (
            "mod M {x}",
            StatementKind::ModDeclaration,
            SyntaxKind::ModDeclaration,
        ),
        (
            "struct S {}",
            StatementKind::StructDeclaration,
            SyntaxKind::StructDeclaration,
        ),
        (
            "enum E {A}",
            StatementKind::EnumDeclaration,
            SyntaxKind::EnumDeclaration,
        ),
        (
            "error E {A}",
            StatementKind::ErrorDeclaration,
            SyntaxKind::ErrorDeclaration,
        ),
        (
            "type T = A",
            StatementKind::TypeDeclaration,
            SyntaxKind::TypeDeclaration,
        ),
        (
            "role R {}",
            StatementKind::RoleDeclaration,
            SyntaxKind::RoleDeclaration,
        ),
        (
            "impl T {}",
            StatementKind::ImplDeclaration,
            SyntaxKind::ImplDeclaration,
        ),
        (
            "cast(x): A = value",
            StatementKind::CastDeclaration,
            SyntaxKind::CastDeclaration,
        ),
        (
            "act A {}",
            StatementKind::ActDeclaration,
            SyntaxKind::ActDeclaration,
        ),
        (
            "for x in xs: x",
            StatementKind::ForStatement,
            SyntaxKind::ForStatement,
        ),
        (
            "prefix (?) 70 = value",
            StatementKind::OperatorDefinition,
            SyntaxKind::OperatorHeader,
        ),
    ] {
        let mut row = trailing(owner, accepted_owner);
        row.prefix = prefix;
        rows.push(row);
    }
    rows.push(Row {
        prefix: "prefix (?) 70 = ",
        before_error: "",
        malformed: "@@",
        after_error: "value",
        role: GrammarRole::Statement(StatementRole::OperatorDefinitionBody),
        expectations: BODY_EXPECTATIONS,
        before_group: vec![SyntaxKind::OperatorHeader],
        after_group: vec![
            (SyntaxKind::OperatorChain, "value"),
            (SyntaxKind::OperatorChain, "next"),
        ],
    });

    for row in rows {
        let source = format!(
            "{}{}{}{}\r\nnext",
            row.prefix, row.before_error, row.malformed, row.after_error
        );
        let error_start = source.find(row.malformed).unwrap();
        let error_end = error_start + row.malformed.len();
        let header = discover_header(&source);
        let fresh = parse_root_candidate(&source, &OperatorTable::empty(), &header.recoveries);
        assert_eq!(fresh.green.to_string(), source, "{source:?}");
        assert_eq!(fresh.committed_recoveries.len(), 1, "{source:?}");
        let record = &fresh.committed_recoveries[0];
        assert_eq!(record.kind, RecoveryKind::Error, "{source:?}");
        assert_eq!(record.site.role, row.role, "{source:?}");
        assert_eq!(record.site.range, error_start..error_end, "{source:?}");
        assert_eq!(
            record.expectations.len(),
            row.expectations.len(),
            "{source:?}"
        );
        for (expectation, expected) in record.expectations.iter().zip(row.expectations) {
            assert_eq!(expectation.role, row.role, "{source:?}");
            assert_eq!(expectation.range, error_start..error_end, "{source:?}");
            assert_eq!(expectation.expected, *expected, "{source:?}");
        }

        let syntax = SyntaxNode::new_root(fresh.green);
        let groups = recovery_groups(&syntax);
        assert_eq!(groups.len(), 1, "{source:?}: {groups:#?}");
        let error = &groups[0];
        assert_eq!(error.parent(), Some(syntax.clone()), "{source:?}");
        assert_eq!(
            error.text_range(),
            rowan::TextRange::new((error_start as u32).into(), (error_end as u32).into()),
            "{source:?}"
        );
        assert_eq!(error.to_string(), row.malformed, "{source:?}");
        let raw_error = error
            .children_with_tokens()
            .filter_map(|element| element.into_token())
            .collect::<Vec<_>>();
        assert!(!raw_error.is_empty(), "{source:?}");
        assert!(
            raw_error
                .iter()
                .all(|token| token.kind() == SyntaxKind::Error
                    && token.parent() == Some(syntax.clone())),
            "{source:?}: {raw_error:#?}"
        );
        assert_eq!(
            raw_error
                .iter()
                .map(|token| token.text())
                .collect::<String>(),
            row.malformed,
            "{source:?}"
        );
        assert!(
            syntax
                .descendants()
                .all(|node| node.kind() != SyntaxKind::Invalid),
            "{source:?}: {syntax:#?}"
        );
        let mut root_order = Vec::new();
        for element in syntax.children_with_tokens() {
            match element {
                rowan::NodeOrToken::Node(node) => {
                    root_order.push(Some((node.kind(), node.text().to_string())))
                }
                rowan::NodeOrToken::Token(token) if token.kind() == SyntaxKind::Error => {
                    if root_order.last().is_none_or(|element| element.is_some()) {
                        root_order.push(None);
                    }
                }
                rowan::NodeOrToken::Token(_) => {}
            }
        }
        let expected_order = row
            .before_group
            .iter()
            .copied()
            .map(|kind| Some((kind, "".to_owned())))
            .chain(std::iter::once(None))
            .chain(
                row.after_group
                    .iter()
                    .map(|&(kind, text)| Some((kind, text.to_owned()))),
            )
            .collect::<Vec<_>>();
        assert_eq!(
            root_order
                .iter()
                .map(|element| element.as_ref().map(|(kind, _)| *kind))
                .collect::<Vec<_>>(),
            expected_order
                .iter()
                .map(|element| element.as_ref().map(|(kind, _)| *kind))
                .collect::<Vec<_>>(),
            "{source:?}: {syntax:#?}"
        );
        for (actual, expected) in root_order.iter().zip(expected_order) {
            if let (Some((_, actual)), Some((_, expected))) = (actual, expected) {
                if !expected.is_empty() {
                    assert_eq!(actual, &expected, "{source:?}");
                }
            }
        }
    }
}

#[test]
fn root_operator_body_missing_gap_and_empty_body_keep_typed_owner() {
    use crate::recovery_record::{ExpectedSyntax, LayoutRole, RecoveryKind};
    for (source, role, at, expected) in [
        (
            "prefix (?) 70 =value",
            GrammarRole::Layout(LayoutRole::InlineTrivia),
            15,
            ExpectedSyntax::InlineTrivia,
        ),
        (
            "prefix (?) 70 =\r\nuse good",
            GrammarRole::Statement(StatementRole::OperatorDefinitionBody),
            15,
            ExpectedSyntax::Expression,
        ),
    ] {
        let header = discover_header(source);
        let root = parse_root_candidate(source, &OperatorTable::empty(), &header.recoveries);
        assert_eq!(root.green.to_string(), source);
        assert_eq!(root.committed_recoveries.len(), 1);
        let record = &root.committed_recoveries[0];
        assert_eq!(record.site.role, role);
        assert_eq!(record.site.range, at..at);
        assert_eq!(record.kind, RecoveryKind::Missing);
        assert_eq!(record.expectations[0].expected, expected);
    }
}

#[test]
fn later_use_recovery_allocates_above_seeded_leading_header_identity() {
    use crate::recovery_record::DiagnosticId;
    let source = "use a as\nmy x = 1\nuse b as";
    let mut header = discover_header(source);
    assert_eq!(header.recoveries.len(), 1);
    header.recoveries[0].id = DiagnosticId(41);
    let root = parse_root_candidate(source, &OperatorTable::empty(), &header.recoveries);
    assert_eq!(root.green.to_string(), source);
    assert_eq!(root.committed_recoveries.len(), 2);
    assert_eq!(root.committed_recoveries[0], header.recoveries[0]);
    assert_eq!(root.committed_recoveries[1].id, DiagnosticId(42));
}

#[test]
fn operator_body_error_is_root_sibling_and_cannot_retry_into_later_header() {
    use crate::recovery_record::RecoveryKind;
    for source in [
        "prefix (?) 70 = @@value\nuse a as",
        "prefix (?) 70 = @@\nuse a as",
    ] {
        let header = discover_header(source);
        let root = parse_root_candidate(source, &OperatorTable::empty(), &header.recoveries);
        assert_eq!(root.green.to_string(), source);
        let body_records = root
            .committed_recoveries
            .iter()
            .filter(|record| {
                record.site.role == GrammarRole::Statement(StatementRole::OperatorDefinitionBody)
            })
            .collect::<Vec<_>>();
        assert_eq!(body_records[0].kind, RecoveryKind::Error);
        assert_eq!(body_records[0].site.range, 16..18);
        if source.contains("@@\n") {
            assert_eq!(body_records.len(), 2);
            assert_eq!(body_records[1].kind, RecoveryKind::Missing);
            assert_eq!(body_records[1].site.range, 18..18);
        } else {
            assert_eq!(body_records.len(), 1);
        }
        assert_eq!(root.committed_recoveries.last(), header.recoveries.last());
        let syntax = SyntaxNode::new_root(root.green);
        let groups = recovery_groups(&syntax);
        let trailing = groups
            .iter()
            .find(|group| group.parent().as_ref() == Some(&syntax))
            .unwrap();
        assert_eq!(trailing.text(), "@@");
        assert_eq!(
            trailing.text_range(),
            rowan::TextRange::new(16.into(), 18.into())
        );
    }
}

#[test]
fn root_operator_header_body_and_trailing_errors_are_direct_and_ordered() {
    let parse = |source| {
        let header = discover_header(source);
        let root = parse_root_candidate(source, &OperatorTable::empty(), &header.recoveries);
        assert_eq!(root.green.to_string(), source, "{source:?}");
        SyntaxNode::new_root(root.green)
    };
    let direct = |syntax: &SyntaxNode| {
        syntax
            .children_with_tokens()
            .map(|element| {
                (
                    element.kind(),
                    usize::from(element.text_range().start())
                        ..usize::from(element.text_range().end()),
                )
            })
            .collect::<Vec<_>>()
    };
    let assert_no_invalid = |syntax: &SyntaxNode| {
        assert!(
            syntax
                .descendants()
                .all(|node| node.kind() != SyntaxKind::Invalid),
            "{syntax:#?}"
        );
    };

    let syntax = parse("prefix (?) @@ = @@");
    assert_eq!(
        direct(&syntax),
        [
            (SyntaxKind::OperatorHeader, 0..15),
            (SyntaxKind::Whitespace, 15..16),
            (SyntaxKind::Error, 16..17),
            (SyntaxKind::Error, 17..18),
            (SyntaxKind::Missing, 18..18),
        ]
    );
    let header = syntax.children().next().unwrap();
    assert_eq!(header.kind(), SyntaxKind::OperatorHeader);
    assert_eq!(
        direct(&header),
        [
            (SyntaxKind::PrefixKw, 0..6),
            (SyntaxKind::Whitespace, 6..7),
            (SyntaxKind::OperatorName, 7..10),
            (SyntaxKind::Whitespace, 10..11),
            (SyntaxKind::Error, 11..12),
            (SyntaxKind::Error, 12..13),
            (SyntaxKind::Whitespace, 13..14),
            (SyntaxKind::Equals, 14..15),
        ]
    );
    let groups = recovery_groups(&syntax);
    assert_eq!(groups.len(), 2);
    assert_eq!(groups[0].parent(), Some(header));
    assert_eq!(
        groups[0].text_range(),
        rowan::TextRange::new(11.into(), 13.into())
    );
    assert_eq!(groups[1].parent(), Some(syntax.clone()));
    assert_eq!(
        groups[1].text_range(),
        rowan::TextRange::new(16.into(), 18.into())
    );
    let missing = syntax
        .children()
        .find(|node| node.kind() == SyntaxKind::Missing)
        .unwrap();
    assert_eq!(
        missing.text_range(),
        rowan::TextRange::new(18.into(), 18.into())
    );
    assert_eq!(missing.parent(), Some(syntax.clone()));
    assert_no_invalid(&syntax);

    let syntax = parse("prefix (?) 70 @@ value");
    assert_eq!(
        direct(&syntax),
        [
            (SyntaxKind::OperatorHeader, 0..16),
            (SyntaxKind::Whitespace, 16..17),
            (SyntaxKind::Error, 17..22),
        ]
    );
    let header = syntax.children().next().unwrap();
    assert!(
        header
            .children_with_tokens()
            .all(|element| element.kind() != SyntaxKind::Equals)
    );
    let groups = recovery_groups(&syntax);
    assert_eq!(groups.len(), 2);
    assert_eq!(groups[0].parent(), Some(header));
    assert_eq!(
        groups[0].text_range(),
        rowan::TextRange::new(14.into(), 16.into())
    );
    assert_eq!(groups[1].parent(), Some(syntax.clone()));
    assert_eq!(
        groups[1].text_range(),
        rowan::TextRange::new(17.into(), 22.into())
    );
    assert!(
        syntax
            .descendants()
            .all(|node| node.kind() != SyntaxKind::Missing)
    );
    assert_no_invalid(&syntax);

    let syntax = parse("prefix (?) 70 = @@\nuse a as");
    assert_eq!(
        direct(&syntax),
        [
            (SyntaxKind::OperatorHeader, 0..15),
            (SyntaxKind::Whitespace, 15..16),
            (SyntaxKind::Error, 16..17),
            (SyntaxKind::Error, 17..18),
            (SyntaxKind::Missing, 18..18),
            (SyntaxKind::Newline, 18..19),
            (SyntaxKind::UseDeclaration, 19..27),
        ]
    );
    let groups = recovery_groups(&syntax);
    assert_eq!(groups.len(), 1);
    assert_eq!(groups[0].parent(), Some(syntax.clone()));
    assert_eq!(
        groups[0].text_range(),
        rowan::TextRange::new(16.into(), 18.into())
    );
    let missing = syntax
        .descendants()
        .filter(|node| node.kind() == SyntaxKind::Missing)
        .collect::<Vec<_>>();
    assert_eq!(
        missing
            .iter()
            .map(|node| node.text_range())
            .collect::<Vec<_>>(),
        [
            rowan::TextRange::new(18.into(), 18.into()),
            rowan::TextRange::new(27.into(), 27.into()),
        ]
    );
    assert_eq!(missing[0].parent(), Some(syntax.clone()));
    assert_eq!(missing[1].parent().unwrap().kind(), SyntaxKind::UseAlias);
    assert!(
        missing[1]
            .ancestors()
            .any(|node| node.kind() == SyntaxKind::UseDeclaration)
    );
    assert_no_invalid(&syntax);

    let operator = parse("prefix (?) 70 = value @@");
    let standalone = parse("value @@");
    assert_eq!(
        direct(&operator),
        [
            (SyntaxKind::OperatorHeader, 0..15),
            (SyntaxKind::Whitespace, 15..16),
            (SyntaxKind::OperatorChain, 16..21),
            (SyntaxKind::Whitespace, 21..22),
            (SyntaxKind::Error, 22..23),
            (SyntaxKind::Error, 23..24),
        ]
    );
    assert_eq!(
        direct(&standalone),
        [
            (SyntaxKind::OperatorChain, 0..5),
            (SyntaxKind::Whitespace, 5..6),
            (SyntaxKind::Error, 6..7),
            (SyntaxKind::Error, 7..8),
        ]
    );
    for syntax in [&operator, &standalone] {
        let errors = syntax
            .children_with_tokens()
            .filter_map(|element| element.into_token())
            .filter(|token| token.kind() == SyntaxKind::Error)
            .collect::<Vec<_>>();
        assert_eq!(errors.len(), 2);
        assert!(
            errors
                .iter()
                .all(|token| token.parent() == Some(syntax.clone()))
        );
        assert_no_invalid(syntax);
    }
}
