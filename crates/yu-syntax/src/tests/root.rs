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
