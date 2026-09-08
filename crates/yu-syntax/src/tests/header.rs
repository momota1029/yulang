use crate::header::{discover_header, discover_header_with_frozen};
use crate::{HeaderImportForm, HeaderImportRouteSeparator, HeaderStop};

#[test]
fn header_keeps_nonzero_indentation_outside_the_leading_header() {
    let header = discover_header("  use a\nuse b\n");
    assert_eq!(header.coverage, 0..2);
    assert_eq!(header.stop, HeaderStop::FirstNonHeader);
    assert!(header.imports.is_empty());
}

#[test]
fn leading_header_projects_forms_routes_groups_and_stops_before_body() {
    let source = "use std::io::{read, nested::{write, flush}, close}\r\nuse mod math/value\r\nuse realm/tools::format\r\nuse band::support::value\r\nmy x = 1\r\nuse late\r\n";
    let header = discover_header(source);
    assert_eq!(header.coverage, 0..source.find("my x").unwrap());
    assert_eq!(header.stop, HeaderStop::FirstNonHeader);
    assert_eq!(
        header
            .imports
            .iter()
            .map(|x| x.path().join("::"))
            .collect::<Vec<_>>(),
        [
            "std::io::read",
            "std::io::nested::write",
            "std::io::nested::flush",
            "std::io::close",
            "math::value",
            "tools::format",
            "support::value"
        ]
    );
    assert_eq!(header.imports[4].form(), HeaderImportForm::Mod);
    assert_eq!(
        header.imports[4].route().separators(),
        [HeaderImportRouteSeparator::Slash]
    );
    assert_eq!(header.imports[5].form(), HeaderImportForm::Realm);
    assert_eq!(header.imports[6].form(), HeaderImportForm::Band);
    assert!(header.recoveries.is_empty());
}

#[test]
fn projection_failure_discards_only_its_whole_declaration() {
    let source = "use a::{one, two as x as y}\nuse b as c\nuse q::*\nuse x v1\nuse final\n";
    let header = discover_header(source);
    assert_eq!(header.stop, HeaderStop::Eof);
    assert_eq!(header.coverage, 0..source.len());
    assert_eq!(
        header
            .imports
            .iter()
            .map(|x| x.path().join("::"))
            .collect::<Vec<_>>(),
        ["b", "final"]
    );
    assert_eq!(header.imports[0].alias(), Some("c"));
}

#[test]
fn unfulfilled_alias_discards_direct_and_grouped_batches_with_frozen_records() {
    use crate::recovery_record::{
        CommittedRecoveryRecord, DeclarationRole, DiagnosticId, ExpectationSources, ExpectedSyntax,
        GrammarRole, ImportRole, RecoveryKind, RecoverySiteKey, SyntaxExpectation,
        UnexpectedCategory, UnexpectedSyntax,
    };
    use std::sync::Arc;

    for (source, error) in [
        ("use a as\nuse b", false),
        ("use a::{one, two as}\nuse b", false),
        ("use a as @\nuse b", true),
        ("use a::{one, two as @}\nuse b", true),
    ] {
        let fresh = discover_header(source);
        if let Some(close) = source.find('}') {
            assert_eq!(fresh.stop, HeaderStop::FirstNonHeader, "{source}");
            assert_eq!(fresh.coverage, 0..close, "{source}");
            assert!(fresh.imports.is_empty(), "{source}");
        } else {
            assert_eq!(fresh.stop, HeaderStop::Eof, "{source}");
            assert_eq!(fresh.coverage, 0..source.len(), "{source}");
            assert_eq!(fresh.imports.len(), 1, "{source}");
            assert_eq!(fresh.imports[0].path(), ["b"], "{source}");
        }
        let role = GrammarRole::Declaration(DeclarationRole::Import(ImportRole::Alias));
        let range = if error {
            let start = source.find('@').unwrap();
            start..start + 1
        } else {
            let start = source.find("as").unwrap() + 2;
            start..start
        };
        let unexpected = if error {
            Arc::from([UnexpectedSyntax::Token {
                range: range.clone(),
                category: UnexpectedCategory::OtherCharacter,
            }])
        } else {
            Arc::from([])
        };
        assert_eq!(
            &*fresh.recoveries,
            [CommittedRecoveryRecord {
                id: DiagnosticId(0),
                site: RecoverySiteKey {
                    role,
                    range: range.clone()
                },
                kind: if error {
                    RecoveryKind::Error
                } else {
                    RecoveryKind::Missing
                },
                unexpected,
                expectations: Arc::from([SyntaxExpectation {
                    role,
                    expected: ExpectedSyntax::Identifier,
                    range,
                    sources: ExpectationSources::COMMITTED_RECOVERY_RULE,
                }]),
                primary_expectation: 0,
            }],
            "{source}"
        );
        let frozen = discover_header_with_frozen(source, Some(&fresh.recoveries));
        assert_eq!(fresh.imports, frozen.imports, "{source}");
        assert_eq!(fresh.recoveries, frozen.recoveries, "{source}");
    }
}

#[test]
fn recovered_alias_keeps_direct_and_grouped_projection() {
    for source in [
        "use a as @ alias\nuse b",
        "use a::{one, two as @ alias}\nuse b",
    ] {
        let fresh = discover_header(source);
        assert_eq!(fresh.stop, HeaderStop::Eof);
        let aliased = fresh
            .imports
            .iter()
            .find(|fact| fact.alias() == Some("alias"))
            .unwrap();
        assert_eq!(
            aliased.path().last().unwrap(),
            if source.contains('{') { "two" } else { "a" }
        );
        assert_eq!(
            fresh.imports.len(),
            if source.contains('{') { 3 } else { 2 }
        );
        assert_eq!(fresh.recoveries.len(), 1);
        let frozen = discover_header_with_frozen(source, Some(&fresh.recoveries));
        assert_eq!(fresh.imports, frozen.imports);
        assert_eq!(fresh.recoveries, frozen.recoveries);
    }
}

#[test]
fn heredoc_longer_quote_run_does_not_end_the_operator_body() {
    let source =
        "prefix (!) 70 = \"\"\"body\n\"\"\"\"\nuse hidden\n\"\"\"\nuse visible\nmy value = 1";
    let fresh = discover_header(source);
    assert_eq!(fresh.coverage, 0..source.find("my value").unwrap());
    assert_eq!(fresh.operators.len(), 1);
    assert_eq!(fresh.imports.len(), 1);
    assert_eq!(fresh.imports[0].path(), ["visible"]);
    assert!(fresh.recoveries.is_empty());
}

#[test]
fn header_opaque_body_keeps_nested_regions_and_frozen_identity() {
    let source = "use a::\r\ninfix (<+>) 50 51 = {\r\n \"} use hidden\"\r\n '~'\r\n}\r\nuse λ::value\r\nmy x = 1";
    let fresh = discover_header(source);
    assert_eq!(fresh.coverage, 0..source.find("my x").unwrap());
    assert_eq!(fresh.operators.len(), 1);
    assert_eq!(fresh.imports.len(), 1);
    assert_eq!(fresh.imports[0].path(), ["λ", "value"]);
    assert_eq!(fresh.recoveries.len(), 1);
    let frozen = discover_header_with_frozen(source, Some(&fresh.recoveries));
    assert_eq!(fresh.imports, frozen.imports);
    assert_eq!(fresh.operators, frozen.operators);
    assert_eq!(fresh.recoveries, frozen.recoveries);
}

#[test]
fn header_error_keeps_retry_leading_outside_and_does_not_cancel_projection() {
    use crate::recovery_record::{
        DeclarationRole, GrammarRole, ImportRole, RecoveryKind, UnexpectedCategory,
        UnexpectedSyntax,
    };
    let source = "use @ a\r\nuse b\r\n";
    let fresh = discover_header(source);
    assert_eq!(fresh.stop, HeaderStop::Eof);
    assert_eq!(
        fresh
            .imports
            .iter()
            .map(|x| x.path().join("::"))
            .collect::<Vec<_>>(),
        ["a", "b"]
    );
    assert_eq!(fresh.imports[0].range(), &(0..7));
    let [record] = &*fresh.recoveries else {
        panic!("one lexical error");
    };
    assert_eq!(record.kind, RecoveryKind::Error);
    assert_eq!(
        record.site.role,
        GrammarRole::Declaration(DeclarationRole::Import(ImportRole::Path))
    );
    assert_eq!(record.site.range, 4..5);
    assert_eq!(
        &*record.unexpected,
        [UnexpectedSyntax::Token {
            range: 4..5,
            category: UnexpectedCategory::OtherCharacter
        }]
    );
    let frozen = discover_header_with_frozen(source, Some(&fresh.recoveries));
    assert_eq!(fresh.recoveries, frozen.recoveries);
}

#[test]
fn header_body_opaque_string_rule_and_yumark_fence_do_not_expose_header_words() {
    for body in [
        "{ \"%fmt{\"}\"} tail\" }",
        "{ ~\"{\"}\"}\" }",
        "'{\n```raw\n}\nuse hidden\n```\n}",
        "'{\n> ```yulang\n> \"```\"\n> ```\n}",
        "{ \"\"\"one\nuse hidden\n\"\"\" }",
    ] {
        let source = format!("prefix (!) 70 = {body}\nuse visible\nmy value = 1");
        let header = discover_header(&source);
        assert_eq!(
            header.coverage,
            0..source.find("my value").unwrap(),
            "{source}"
        );
        assert_eq!(header.operators.len(), 1, "{source}");
        assert_eq!(header.imports.len(), 1, "{source}");
        assert_eq!(header.imports[0].path(), ["visible"], "{source}");
    }
}
