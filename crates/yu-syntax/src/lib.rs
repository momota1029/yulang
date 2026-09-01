//! Syntax boundary for Yulang3.

use std::{ops::Range, sync::Arc};

mod grammar;
#[allow(dead_code)]
mod input;
#[allow(dead_code)]
mod operator;
mod parse;
#[allow(dead_code)]
mod scan;
#[allow(dead_code)]
mod session;
#[allow(dead_code)]
mod sink;
mod syntax_kind;

pub use operator::{OperatorOrigin, OperatorTable};
pub use parse::{
    OperatorConflictDiagnostic, ParsedFile, SourceRevision, SyntaxDependencyProvenance,
    SyntaxDependencySlot, SyntaxDiagnostic, SyntaxDiagnosticCause, SyntaxEnvironment,
    SyntaxEnvironmentBuildError, SyntaxEnvironmentKey, parse_file,
};
pub use syntax_kind::{SyntaxKind, SyntaxNode, SyntaxToken, YulangLanguage};

/// Source text consumed by syntax phase entrypoints.
pub type SourceText = str;

/// Source-level facts discovered in the syntax preamble.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct HeaderInfo {
    coverage: HeaderCoverage,
    imports: Arc<[HeaderImport]>,
    operators: Arc<[HeaderOperator]>,
}

impl HeaderInfo {
    pub fn coverage(&self) -> &HeaderCoverage {
        &self.coverage
    }

    pub fn imports(&self) -> &[HeaderImport] {
        &self.imports
    }

    pub fn operators(&self) -> &[HeaderOperator] {
        &self.operators
    }
}

/// The source prefix observed while discovering header facts.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct HeaderCoverage {
    range: Range<usize>,
    stop: HeaderStop,
}

impl HeaderCoverage {
    pub fn range(&self) -> &Range<usize> {
        &self.range
    }

    pub fn stop(&self) -> HeaderStop {
        self.stop
    }
}

/// Why header discovery stopped.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum HeaderStop {
    Eof,
    FirstNonHeader,
}

/// An unresolved source-level import discovered in the header.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct HeaderImport {
    range: Range<usize>,
    form: HeaderImportForm,
    route: HeaderImportRoute,
    visibility: Visibility,
    alias: Option<String>,
}

impl HeaderImport {
    pub fn range(&self) -> &Range<usize> {
        &self.range
    }

    pub fn form(&self) -> HeaderImportForm {
        self.form
    }

    pub fn path(&self) -> &[String] {
        self.route.segments()
    }

    /// The source route, preserving the separators between path segments.
    pub fn route(&self) -> &HeaderImportRoute {
        &self.route
    }

    pub fn visibility(&self) -> Visibility {
        self.visibility
    }

    pub fn alias(&self) -> Option<&str> {
        self.alias.as_deref()
    }

    pub(crate) fn new(
        range: Range<usize>,
        form: HeaderImportForm,
        route: HeaderImportRoute,
        visibility: Visibility,
        alias: Option<String>,
    ) -> Self {
        Self {
            range,
            form,
            route,
            visibility,
            alias,
        }
    }
}

/// A separator-preserving source route for an unresolved import.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct HeaderImportRoute {
    segments: Vec<String>,
    separators: Vec<HeaderImportRouteSeparator>,
}

impl HeaderImportRoute {
    pub fn segments(&self) -> &[String] {
        &self.segments
    }

    pub fn separators(&self) -> &[HeaderImportRouteSeparator] {
        &self.separators
    }

    pub(crate) fn new(segments: Vec<String>, separators: Vec<HeaderImportRouteSeparator>) -> Self {
        debug_assert_eq!(
            separators.len(),
            segments.len().saturating_sub(1),
            "an import route has one separator between each path segment"
        );
        Self {
            segments,
            separators,
        }
    }
}

/// A separator in a source-level import route.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum HeaderImportRouteSeparator {
    ColonColon,
    Slash,
}

/// Source-level import form, before module resolution.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum HeaderImportForm {
    Plain,
    Mod,
    Realm,
    Band,
}

/// Source-level visibility of a discovered header fact.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Visibility {
    Private,
    Our,
    Public,
}

/// A dynamic operator signature discovered in the header.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct HeaderOperator {
    range: Range<usize>,
    name: String,
    fixity: OperatorFixity,
    visibility: Visibility,
    lazy: bool,
    binding_power: BindingPowers,
}

impl HeaderOperator {
    pub fn range(&self) -> &Range<usize> {
        &self.range
    }

    pub fn name(&self) -> &str {
        &self.name
    }

    pub fn fixity(&self) -> OperatorFixity {
        self.fixity
    }

    pub fn visibility(&self) -> Visibility {
        self.visibility
    }

    pub fn is_lazy(&self) -> bool {
        self.lazy
    }

    pub fn binding_power(&self) -> &BindingPowers {
        &self.binding_power
    }

    pub(crate) fn new(
        range: Range<usize>,
        name: String,
        fixity: OperatorFixity,
        visibility: Visibility,
        lazy: bool,
        binding_power: BindingPowers,
    ) -> Self {
        Self {
            range,
            name,
            fixity,
            visibility,
            lazy,
            binding_power,
        }
    }
}

/// Canonical operator fixity.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum OperatorFixity {
    Prefix,
    Infix,
    Suffix,
    Nullfix,
}

/// Binding-power sides applicable to one operator declaration.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct BindingPowers {
    left: Option<BindingPower>,
    right: Option<BindingPower>,
}

impl BindingPowers {
    pub fn left(&self) -> Option<&BindingPower> {
        self.left.as_ref()
    }

    pub fn right(&self) -> Option<&BindingPower> {
        self.right.as_ref()
    }

    pub(crate) fn prefix(right: BindingPower) -> Self {
        Self {
            left: None,
            right: Some(right),
        }
    }

    pub(crate) fn infix(left: BindingPower, right: BindingPower) -> Self {
        Self {
            left: Some(left),
            right: Some(right),
        }
    }

    pub(crate) fn suffix(left: BindingPower) -> Self {
        Self {
            left: Some(left),
            right: None,
        }
    }

    pub(crate) fn nullfix() -> Self {
        Self {
            left: None,
            right: None,
        }
    }
}

/// One `BpVec`-equivalent binding-power vector in a header fact.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct BindingPower {
    components: Box<[i8]>,
}

impl BindingPower {
    pub fn components(&self) -> &[i8] {
        &self.components
    }

    pub(crate) fn from_components(components: impl Into<Box<[i8]>>) -> Self {
        Self {
            components: components.into(),
        }
    }
}

/// Discover leading imports and operator signatures.
pub fn scan_header(source: Arc<SourceText>) -> HeaderInfo {
    grammar::header::discover_header(source.as_ref()).into_header_info()
}

#[cfg(test)]
mod tests {
    use super::*;

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
            root.descendants()
                .filter(|node| matches!(node.kind(), SyntaxKind::Missing | SyntaxKind::Error))
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
}
