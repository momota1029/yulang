use crate::*;

#[test]
fn header_debug_contains_only_header_facts() {
    let header = scan_header(Arc::from("private_body_identifier"));
    assert_eq!(
        format!("{header:?}"),
        "HeaderInfo { coverage: HeaderCoverage { range: 0..0, stop: FirstNonHeader }, imports: [], operators: [] }"
    );
    assert!(!format!("{header:#?}").contains("private_body_identifier"));
}

const LEADING_USE_SOURCE: &[u8] = include_bytes!(concat!(
    env!("CARGO_MANIFEST_DIR"),
    "/../../tests/contracts/phase2-parser/v0/cases/leading-use-plain/main.yu"
));
const INFIX_OPERATOR_SOURCE: &[u8] = include_bytes!(concat!(
    env!("CARGO_MANIFEST_DIR"),
    "/../../tests/contracts/phase2-parser/v0/cases/infix-operator-header/main.yu"
));

#[test]
fn discovers_leading_plain_use_fixture() {
    let header = scan_header(fixture_source(LEADING_USE_SOURCE));

    assert_eq!(header.coverage().range(), &(0..14));
    assert_eq!(header.coverage().stop(), HeaderStop::FirstNonHeader);
    assert!(header.operators().is_empty());

    let [import] = header.imports() else {
        panic!("expected exactly one header import: {header:#?}");
    };
    assert_eq!(import.range(), &(0..13));
    assert_eq!(import.form(), HeaderImportForm::Plain);
    assert_eq!(import.path(), ["std".to_owned(), "data".to_owned()]);
    assert_eq!(import.visibility(), Visibility::Private);
    assert_eq!(import.alias(), None);
}

#[test]
fn discovers_simple_use_forms_with_marker_specific_routes() {
    let cases = [
        (
            "use std::data\n",
            HeaderImportForm::Plain,
            &["std", "data"] as &[_],
            &[HeaderImportRouteSeparator::ColonColon][..],
        ),
        (
            "use mod math::value\n",
            HeaderImportForm::Mod,
            &["math", "value"],
            &[HeaderImportRouteSeparator::ColonColon][..],
        ),
        (
            "use realm/tools::format\n",
            HeaderImportForm::Realm,
            &["tools", "format"],
            &[HeaderImportRouteSeparator::ColonColon][..],
        ),
        (
            "use band::support::value\n",
            HeaderImportForm::Band,
            &["support", "value"],
            &[HeaderImportRouteSeparator::ColonColon][..],
        ),
    ];

    for (source, form, path, separators) in cases {
        let header = scan_header(Arc::from(source));

        assert_eq!(header.coverage().range(), &(0..source.len()), "{source}");
        assert_eq!(header.coverage().stop(), HeaderStop::Eof, "{source}");
        let [import] = header.imports() else {
            panic!("expected exactly one header import: {header:#?}");
        };
        assert_eq!(import.form(), form, "{source}");
        assert_eq!(import.path(), path, "{source}");
        assert_eq!(import.route().separators(), separators, "{source}");
    }
}

#[test]
fn keeps_non_marker_use_paths_plain() {
    let cases = [
        (
            "use realm::tools\n",
            &["realm", "tools"] as &[_],
            &[HeaderImportRouteSeparator::ColonColon][..],
        ),
        (
            "use band/tools\n",
            &["band", "tools"],
            &[HeaderImportRouteSeparator::Slash][..],
        ),
        (
            "use package/tools::format\n",
            &["package", "tools", "format"],
            &[
                HeaderImportRouteSeparator::Slash,
                HeaderImportRouteSeparator::ColonColon,
            ][..],
        ),
    ];

    for (source, path, separators) in cases {
        let header = scan_header(Arc::from(source));
        let [import] = header.imports() else {
            panic!("expected exactly one header import: {header:#?}");
        };
        assert_eq!(import.form(), HeaderImportForm::Plain, "{source}");
        assert_eq!(import.path(), path, "{source}");
        assert_eq!(import.route().separators(), separators, "{source}");
    }
}

#[test]
fn parses_simple_use_forms_losslessly() {
    for source in [
        "use std::data\nmy value = 1\n",
        "use mod math::value\nmy value = 1\n",
        "use realm/tools::format\nmy value = 1\n",
        "use band::support::value\nmy value = 1\n",
    ] {
        let source: Arc<SourceText> = Arc::from(source);
        let header = Arc::new(scan_header(Arc::clone(&source)));
        let parsed = parse_file(
            Arc::clone(&source),
            header,
            Arc::new(SyntaxEnvironment::empty()),
        );

        assert_eq!(parsed.green().to_string(), source.as_ref());
        assert!(parsed.diagnostics().is_empty());
    }
}

#[test]
fn discovers_infix_operator_header_fixture() {
    let header = scan_header(fixture_source(INFIX_OPERATOR_SOURCE));

    assert_eq!(header.coverage().range(), &(0..25));
    assert_eq!(header.coverage().stop(), HeaderStop::FirstNonHeader);
    assert!(header.imports().is_empty());

    let [operator] = header.operators() else {
        panic!("expected exactly one header operator: {header:#?}");
    };
    assert_eq!(operator.range(), &(0..19));
    assert_eq!(operator.name(), "<+>");
    assert_eq!(operator.fixity(), OperatorFixity::Infix);
    assert_eq!(operator.visibility(), Visibility::Private);
    assert_eq!(
        operator
            .binding_power()
            .left()
            .map(BindingPower::components),
        Some(&[50][..])
    );
    assert_eq!(
        operator
            .binding_power()
            .right()
            .map(BindingPower::components),
        Some(&[51][..])
    );
}

#[test]
fn parses_leading_plain_use_fixture_losslessly() {
    let source = fixture_source(LEADING_USE_SOURCE);
    let header = Arc::new(scan_header(Arc::clone(&source)));
    let parsed = parse_file(
        Arc::clone(&source),
        Arc::clone(&header),
        Arc::new(SyntaxEnvironment::empty()),
    );

    assert_eq!(parsed.green().to_string(), source.as_ref());
    assert!(parsed.diagnostics().is_empty());
    assert_eq!(parsed.revision(), SourceRevision::UNTRACKED);
    assert_eq!(parsed.syntax_environment(), SyntaxEnvironmentKey::EMPTY);

    let root = SyntaxNode::new_root(parsed.green().clone());
    let use_declaration = node_of_kind(&root, SyntaxKind::UseDeclaration);
    let [import] = header.imports() else {
        panic!("expected exactly one header import: {header:#?}");
    };
    assert_eq!(node_range(&use_declaration), import.range().clone());
    assert_eq!(
        token_texts(&use_declaration, SyntaxKind::Identifier),
        import.path()
    );
    assert_eq!(token_texts(&use_declaration, SyntaxKind::UseKw), ["use"]);
    assert_eq!(
        token_texts(&use_declaration, SyntaxKind::ColonColon),
        ["::"]
    );
    assert_eq!(import.form(), HeaderImportForm::Plain);
    assert_eq!(import.visibility(), Visibility::Private);
    assert_eq!(import.alias(), None);

    let binding = node_of_kind(&root, SyntaxKind::BindingStatement);
    assert_eq!(binding.to_string(), "my value = 1");
    assert_eq!(
        node_of_kind(&binding, SyntaxKind::IntegerLiteral).to_string(),
        "1"
    );
}

#[test]
fn parses_infix_operator_header_fixture_losslessly() {
    let source = fixture_source(INFIX_OPERATOR_SOURCE);
    let header = Arc::new(scan_header(Arc::clone(&source)));
    let parsed = parse_file(
        Arc::clone(&source),
        Arc::clone(&header),
        Arc::new(SyntaxEnvironment::empty()),
    );

    assert_eq!(parsed.green().to_string(), source.as_ref());
    assert!(parsed.diagnostics().is_empty());

    let root = SyntaxNode::new_root(parsed.green().clone());
    let operator_header = node_of_kind(&root, SyntaxKind::OperatorHeader);
    let [operator] = header.operators() else {
        panic!("expected exactly one header operator: {header:#?}");
    };
    assert_eq!(node_range(&operator_header), operator.range().clone());
    assert_eq!(
        token_texts(&operator_header, SyntaxKind::InfixKw),
        ["infix"]
    );
    assert_eq!(
        token_texts(&operator_header, SyntaxKind::Operator),
        [operator.name()]
    );
    let binding_powers = token_texts(&operator_header, SyntaxKind::Integer)
        .into_iter()
        .map(|text| {
            text.parse::<i8>()
                .expect("fixture binding power must fit i8")
        })
        .collect::<Vec<_>>();
    assert_eq!(
        binding_powers,
        [
            operator.binding_power().left().unwrap().components()[0],
            operator.binding_power().right().unwrap().components()[0],
        ]
    );
    assert_eq!(operator.fixity(), OperatorFixity::Infix);
    assert_eq!(operator.visibility(), Visibility::Private);

    let binding = node_of_kind(&root, SyntaxKind::BindingStatement);
    assert_eq!(binding.to_string(), "my value = 1");
    assert_eq!(
        node_of_kind(&binding, SyntaxKind::IntegerLiteral).to_string(),
        "1"
    );
}

// GATE10_PUBLIC_PRODUCTION_COMPANION_PERFORMANCE_HARNESS_BEGIN
// Harness identity: gate10-public-production-companion-v1.
#[test]
#[ignore = "manual Gate 10 public production companion measurement"]
fn gate10_public_production_companion_performance_harness() {
    use std::{hint::black_box, time::Instant};

    const DECLARATION_COUNT: usize = 10_000;
    const INTERNAL_REPEATS: usize = 8;
    const DECLARATION: &str = "struct S {} with { my value = value }";

    let mut source = String::with_capacity(
        DECLARATION_COUNT * DECLARATION.len() + DECLARATION_COUNT.saturating_sub(1),
    );
    for index in 0..DECLARATION_COUNT {
        if index != 0 {
            source.push('\n');
        }
        source.push_str(DECLARATION);
    }
    let source: Arc<SourceText> = Arc::from(source);
    let header = Arc::new(scan_header(Arc::clone(&source)));
    let syntax = Arc::new(SyntaxEnvironment::empty());

    let mut retained = None;
    let kernel_start = Instant::now();
    for _ in 0..INTERNAL_REPEATS {
        retained = Some(parse_file(
            Arc::clone(&source),
            Arc::clone(&header),
            Arc::clone(&syntax),
        ));
        black_box(retained.as_ref());
    }
    let kernel_elapsed = kernel_start.elapsed();

    let parsed = retained.expect("the eight-repeat kernel retains its final ParsedFile");
    let root = SyntaxNode::new_root(parsed.green().clone());
    assert_eq!(root.to_string(), source.as_ref());
    assert!(parsed.diagnostics().is_empty());
    assert_eq!(
        root.descendants_with_tokens()
            .filter(|node| matches!(
                node.kind(),
                SyntaxKind::Missing | SyntaxKind::Error | SyntaxKind::Invalid
            ))
            .count(),
        0,
    );
    assert_eq!(
        root.descendants()
            .filter(|node| node.kind() == SyntaxKind::StructDeclaration)
            .count(),
        DECLARATION_COUNT,
    );
    assert_eq!(
        root.descendants()
            .filter(|node| node.kind() == SyntaxKind::DeclarationCompanion)
            .count(),
        DECLARATION_COUNT,
    );
    println!(
        "GATE10_PUBLIC_PRODUCTION_COMPANION_KERNEL_SECONDS={:.9}",
        kernel_elapsed.as_secs_f64(),
    );
}
// GATE10_PUBLIC_PRODUCTION_COMPANION_PERFORMANCE_HARNESS_END

fn node_of_kind(root: &SyntaxNode, kind: SyntaxKind) -> SyntaxNode {
    root.descendants()
        .find(|node| node.kind() == kind)
        .unwrap_or_else(|| panic!("expected {kind:?} in CST:\n{root:#?}"))
}

fn node_range(node: &SyntaxNode) -> Range<usize> {
    let range = node.text_range();
    u32::from(range.start()) as usize..u32::from(range.end()) as usize
}

fn token_texts(node: &SyntaxNode, kind: SyntaxKind) -> Vec<String> {
    node.descendants_with_tokens()
        .filter_map(rowan::NodeOrToken::into_token)
        .filter(|token| token.kind() == kind)
        .map(|token| token.text().to_owned())
        .collect()
}

fn fixture_source(bytes: &'static [u8]) -> Arc<SourceText> {
    Arc::from(std::str::from_utf8(bytes).expect("fixture source must be valid UTF-8"))
}
