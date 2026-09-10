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
