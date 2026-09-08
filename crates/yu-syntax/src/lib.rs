//! Syntax boundary for Yulang3.

use std::{ops::Range, sync::Arc};

mod ambient_claim;
mod cst_output;
mod cursor;
mod declaration;
mod expression;
mod handoff;
mod header;
mod lexical;
mod literal;
mod operator_table;
mod parse;
mod pattern;
mod recovery_record;
mod rule;
mod sequence;
mod source_file;
mod statement;
mod syntax_kind;
mod type_expr;
mod virtual_statement_block;

pub use operator_table::{OperatorOrigin, OperatorTable};
pub use parse::{
    OperatorConflictDiagnostic, ParsedFile, SourceRevision, SyntaxDependencyProvenance,
    SyntaxDependencySlot, SyntaxDiagnostic, SyntaxDiagnosticCause, SyntaxEnvironment,
    SyntaxEnvironmentBuildError, SyntaxEnvironmentKey, parse_file,
};
pub use syntax_kind::{SyntaxKind, SyntaxNode, SyntaxToken, YulangLanguage};

/// Source text consumed by syntax phase entrypoints.
pub type SourceText = str;

/// Source-level facts discovered in the syntax preamble.
#[derive(Clone, Eq)]
pub struct HeaderInfo {
    source: Arc<SourceText>,
    recoveries: Arc<[recovery_record::CommittedRecoveryRecord]>,
    coverage: HeaderCoverage,
    imports: Arc<[HeaderImport]>,
    operators: Arc<[HeaderOperator]>,
}

impl std::fmt::Debug for HeaderInfo {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("HeaderInfo")
            .field("coverage", &self.coverage)
            .field("imports", &self.imports)
            .field("operators", &self.operators)
            .finish()
    }
}

impl PartialEq for HeaderInfo {
    fn eq(&self, other: &Self) -> bool {
        self.coverage == other.coverage
            && self.imports == other.imports
            && self.operators == other.operators
    }
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
    header::discover_header(source.as_ref()).into_header_info(source)
}

#[cfg(test)]
mod tests;
