use std::{ops::Range, sync::Arc};

use rowan::{GreenNode, GreenNodeBuilder};

use crate::{
    Delimiter, HeaderCursor, HeaderInfo, HeaderKeyword, OperatorFixity, ScanItem, SourceText,
    TokenKind, TriviaKind,
    operator::{OperatorOrigin, OperatorTable, compile_full_parse_operators_recovering},
    session::CommittedRecoveryRecord,
    syntax_kind::SyntaxKind,
};

/// Syntax facts selected for one full parse.
#[derive(Clone, Debug)]
pub struct SyntaxEnvironment {
    key: SyntaxEnvironmentKey,
    operators: Arc<OperatorTable>,
    provenance: Arc<[SyntaxDependencyProvenance]>,
}

impl SyntaxEnvironment {
    /// Construct an environment with no imported dynamic operators.
    pub fn empty() -> Self {
        Self {
            key: SyntaxEnvironmentKey::EMPTY,
            operators: Arc::new(OperatorTable::empty()),
            provenance: Arc::from([]),
        }
    }

    /// Validates and stores the imported-only syntax facts selected for one consumer file.
    pub fn from_imported(
        key: SyntaxEnvironmentKey,
        operators: Arc<OperatorTable>,
        provenance: Arc<[SyntaxDependencyProvenance]>,
    ) -> Result<Self, SyntaxEnvironmentBuildError> {
        for (entry, sites) in operators.entries_with_sites() {
            for fixity in [
                OperatorFixity::Prefix,
                OperatorFixity::Infix,
                OperatorFixity::Suffix,
                OperatorFixity::Nullfix,
            ] {
                let Some(site) = sites.site(fixity) else {
                    continue;
                };
                match site.origin() {
                    OperatorOrigin::Local => {
                        return Err(
                            SyntaxEnvironmentBuildError::ImportedTableContainsLocalOrigin {
                                spelling: entry.spelling().into(),
                                fixity,
                                range: site.range().clone(),
                            },
                        );
                    }
                    OperatorOrigin::Imported(dependency)
                        if provenance.get(dependency.index()).is_none() =>
                    {
                        return Err(SyntaxEnvironmentBuildError::MissingDependencyProvenance {
                            spelling: entry.spelling().into(),
                            fixity,
                            dependency,
                            range: site.range().clone(),
                        });
                    }
                    OperatorOrigin::Imported(_) => {}
                }
            }
        }

        Ok(Self {
            key,
            operators,
            provenance,
        })
    }

    pub fn key(&self) -> SyntaxEnvironmentKey {
        self.key
    }

    pub fn operators(&self) -> &OperatorTable {
        &self.operators
    }

    pub fn provenance(&self) -> &[SyntaxDependencyProvenance] {
        &self.provenance
    }

    pub fn dependency(&self, slot: SyntaxDependencySlot) -> Option<&SyntaxDependencyProvenance> {
        self.provenance.get(slot.index())
    }
}

impl Default for SyntaxEnvironment {
    fn default() -> Self {
        Self::empty()
    }
}

/// Immutable full-parse product for one source revision.
#[derive(Clone, Debug)]
pub struct ParsedFile {
    source: Arc<SourceText>,
    revision: SourceRevision,
    header: Arc<HeaderInfo>,
    syntax_environment: SyntaxEnvironmentKey,
    green: GreenNode,
    diagnostics: Arc<[SyntaxDiagnostic]>,
}

impl ParsedFile {
    pub fn source(&self) -> &SourceText {
        &self.source
    }

    pub fn revision(&self) -> SourceRevision {
        self.revision
    }

    pub fn header(&self) -> &HeaderInfo {
        &self.header
    }

    pub fn syntax_environment(&self) -> SyntaxEnvironmentKey {
        self.syntax_environment
    }

    pub fn green(&self) -> &GreenNode {
        &self.green
    }

    pub fn diagnostics(&self) -> &[SyntaxDiagnostic] {
        &self.diagnostics
    }
}

/// Parse a source with its discovered header and selected syntax environment.
pub fn parse_file(
    source: Arc<SourceText>,
    header: Arc<HeaderInfo>,
    syntax: Arc<SyntaxEnvironment>,
) -> ParsedFile {
    // Construction is deliberately separate from the old CST entrypoint.  The
    // accepted table is prepared once so duplicate capabilities produce their
    // construction diagnostics without replacing this parser authority.
    let operator_compilation = compile_full_parse_operators_recovering(
        syntax.operators(),
        header.operators(),
    )
    .expect("complete header operators and validated imports never have empty spellings");
    let green = FullCstBuilder::new(source.as_ref(), header.as_ref()).build();
    let diagnostics = operator_compilation
        .rejected_conflicts
        .into_iter()
        .enumerate()
        .map(|(event, conflict)| SyntaxDiagnostic::conflicting_operator_fixity(event as u32, conflict))
        .collect();

    ParsedFile {
        source,
        revision: SourceRevision::UNTRACKED,
        header,
        syntax_environment: syntax.key(),
        green,
        diagnostics,
    }
}

/// Opaque identity of the syntax inputs selected for a parse.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct SyntaxEnvironmentKey(u64);

impl SyntaxEnvironmentKey {
    pub const EMPTY: Self = Self(0);
}

/// Environment-local ordinal identifying a syntax dependency provenance record.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct SyntaxDependencySlot(u32);

impl SyntaxDependencySlot {
    pub fn from_index(index: usize) -> Option<Self> {
        u32::try_from(index).ok().map(Self)
    }

    pub fn index(self) -> usize {
        self.0 as usize
    }
}

/// Provenance for one syntax dependency selected by syntax planning.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SyntaxDependencyProvenance {
    module_label: Arc<str>,
    revision: SourceRevision,
}

impl SyntaxDependencyProvenance {
    pub fn new(module_label: Arc<str>, revision: SourceRevision) -> Self {
        Self {
            module_label,
            revision,
        }
    }

    pub fn module_label(&self) -> &str {
        &self.module_label
    }

    pub fn revision(&self) -> SourceRevision {
        self.revision
    }
}

/// Rejection from the imported syntax-environment construction boundary.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum SyntaxEnvironmentBuildError {
    ImportedTableContainsLocalOrigin {
        spelling: Box<str>,
        fixity: OperatorFixity,
        range: Range<usize>,
    },
    MissingDependencyProvenance {
        spelling: Box<str>,
        fixity: OperatorFixity,
        dependency: SyntaxDependencySlot,
        range: Range<usize>,
    },
}

/// Identity of the source snapshot represented by a phase product.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct SourceRevision(u64);

impl SourceRevision {
    /// Placeholder used until revision allocation is owned by compiler queries.
    pub const UNTRACKED: Self = Self(0);
}

/// Structured syntax diagnostic owned by the syntax phase.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SyntaxDiagnostic {
    id: u32,
    primary: Range<usize>,
    cause: SyntaxDiagnosticCause,
}

impl SyntaxDiagnostic {
    pub(crate) fn recovery(record: CommittedRecoveryRecord) -> Self {
        Self {
            id: record.id.0,
            primary: record.site.range.clone(),
            cause: SyntaxDiagnosticCause::Recovery(RecoveryDiagnostic { record }),
        }
    }

    fn conflicting_operator_fixity(
        id: u32,
        conflict: crate::operator::RejectedOperatorFixity,
    ) -> Self {
        let primary = conflict.second_range.clone();
        Self {
            id,
            primary,
            cause: SyntaxDiagnosticCause::ConflictingOperatorFixity(OperatorConflictDiagnostic {
                spelling: conflict.spelling,
                fixity: conflict.fixity,
                first_origin: conflict.first_origin,
                first_range: conflict.first_range,
                second_origin: conflict.second_origin,
                second_range: conflict.second_range,
            }),
        }
    }

    pub fn id(&self) -> u32 {
        self.id
    }

    pub fn primary(&self) -> &Range<usize> {
        &self.primary
    }

    pub fn cause(&self) -> &SyntaxDiagnosticCause {
        &self.cause
    }
}

/// The typed cause of a syntax diagnostic.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum SyntaxDiagnosticCause {
    /// A committed grammar recovery, distinct from semantic table construction.
    Recovery(RecoveryDiagnostic),
    ConflictingOperatorFixity(OperatorConflictDiagnostic),
}

/// The committed recovery record behind a recovery diagnostic.
///
/// Its typed site, unexpected evidence, and expectation union remain an
/// internal grammar vocabulary until the diagnostic presentation API is
/// versioned, but no information is collapsed into a message string here.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct RecoveryDiagnostic {
    record: CommittedRecoveryRecord,
}

impl RecoveryDiagnostic {
    pub(crate) fn record(&self) -> &CommittedRecoveryRecord {
        &self.record
    }
}

/// One rejected operator capability and the already-accepted conflicting site.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct OperatorConflictDiagnostic {
    spelling: Box<str>,
    fixity: OperatorFixity,
    first_origin: OperatorOrigin,
    first_range: Range<usize>,
    second_origin: OperatorOrigin,
    second_range: Range<usize>,
}

impl OperatorConflictDiagnostic {
    pub fn spelling(&self) -> &str {
        &self.spelling
    }

    pub fn fixity(&self) -> OperatorFixity {
        self.fixity
    }

    pub fn first_origin(&self) -> OperatorOrigin {
        self.first_origin
    }

    pub fn first_range(&self) -> &Range<usize> {
        &self.first_range
    }

    pub fn second_origin(&self) -> OperatorOrigin {
        self.second_origin
    }

    pub fn second_range(&self) -> &Range<usize> {
        &self.second_range
    }
}

struct FullCstBuilder<'source, 'header> {
    source: &'source str,
    header: &'header HeaderInfo,
    tokens: Vec<LexedToken>,
    token_index: usize,
    builder: GreenNodeBuilder<'static>,
}

impl<'source, 'header> FullCstBuilder<'source, 'header> {
    fn new(source: &'source str, header: &'header HeaderInfo) -> Self {
        Self {
            source,
            header,
            tokens: lex(source),
            token_index: 0,
            builder: GreenNodeBuilder::new(),
        }
    }

    fn build(mut self) -> GreenNode {
        self.start_node(SyntaxKind::Root);
        self.emit_header();
        self.emit_binding_statement();
        self.emit_remaining();
        self.finish_node();
        self.builder.finish()
    }

    fn emit_header(&mut self) {
        let mut import_index = 0;
        let mut operator_index = 0;

        // HeaderInfo owns the committed declaration facts. The full CST uses
        // those ranges as node boundaries instead of creating a second header
        // grammar authority, while all bytes still come from the shared lexer.
        while let Some(declaration) = self.next_header_node(&mut import_index, &mut operator_index)
        {
            self.emit_until(declaration.range.start);
            self.start_node(declaration.kind);
            self.emit_until(declaration.range.end);
            self.finish_node();
        }

        self.emit_until(self.header.coverage().range().end);
    }

    fn next_header_node(
        &self,
        import_index: &mut usize,
        operator_index: &mut usize,
    ) -> Option<HeaderNode> {
        let import = self.header.imports().get(*import_index);
        let operator = self.header.operators().get(*operator_index);

        match (import, operator) {
            (Some(import), Some(operator)) if import.range().start <= operator.range().start => {
                *import_index += 1;
                Some(HeaderNode {
                    kind: SyntaxKind::UseDeclaration,
                    range: import.range().clone(),
                })
            }
            (Some(_), Some(operator)) => {
                *operator_index += 1;
                Some(HeaderNode {
                    kind: SyntaxKind::OperatorHeader,
                    range: operator.range().clone(),
                })
            }
            (Some(import), None) => {
                *import_index += 1;
                Some(HeaderNode {
                    kind: SyntaxKind::UseDeclaration,
                    range: import.range().clone(),
                })
            }
            (None, Some(operator)) => {
                *operator_index += 1;
                Some(HeaderNode {
                    kind: SyntaxKind::OperatorHeader,
                    range: operator.range().clone(),
                })
            }
            (None, None) => None,
        }
    }

    fn emit_binding_statement(&mut self) {
        const BINDING_SHAPE: [SyntaxKind; 7] = [
            SyntaxKind::MyKw,
            SyntaxKind::Whitespace,
            SyntaxKind::Identifier,
            SyntaxKind::Whitespace,
            SyntaxKind::Equals,
            SyntaxKind::Whitespace,
            SyntaxKind::Integer,
        ];

        let Some(candidate) = self
            .tokens
            .get(self.token_index..self.token_index + BINDING_SHAPE.len())
        else {
            return;
        };
        if !candidate.iter().map(|token| token.kind).eq(BINDING_SHAPE) {
            return;
        }
        if self
            .tokens
            .get(self.token_index + BINDING_SHAPE.len())
            .is_some_and(|token| token.kind != SyntaxKind::Newline)
        {
            return;
        }

        self.start_node(SyntaxKind::BindingStatement);
        for _ in 0..BINDING_SHAPE.len() - 1 {
            self.emit_token();
        }
        self.start_node(SyntaxKind::IntegerLiteral);
        self.emit_token();
        self.finish_node();
        self.finish_node();
    }

    fn emit_until(&mut self, end: usize) {
        assert!(
            end <= self.source.len(),
            "header range {end} exceeds source length {}",
            self.source.len()
        );

        while self
            .tokens
            .get(self.token_index)
            .is_some_and(|token| token.range.end <= end)
        {
            self.emit_token();
        }

        assert_eq!(
            self.current_offset(),
            end,
            "header range boundary must coincide with a shared token boundary"
        );
    }

    fn emit_remaining(&mut self) {
        while self.token_index < self.tokens.len() {
            self.emit_token();
        }
    }

    fn emit_token(&mut self) {
        let token = &self.tokens[self.token_index];
        self.builder
            .token(token.kind.into(), &self.source[token.range.clone()]);
        self.token_index += 1;
    }

    fn current_offset(&self) -> usize {
        self.tokens
            .get(self.token_index)
            .map_or(self.source.len(), |token| token.range.start)
    }

    fn start_node(&mut self, kind: SyntaxKind) {
        self.builder.start_node(kind.into());
    }

    fn finish_node(&mut self) {
        self.builder.finish_node();
    }
}

struct HeaderNode {
    kind: SyntaxKind,
    range: Range<usize>,
}

struct LexedToken {
    kind: SyntaxKind,
    range: Range<usize>,
}

fn lex(source: &str) -> Vec<LexedToken> {
    let mut cursor = HeaderCursor::new(source);
    let mut tokens = Vec::new();

    while let Some(item) = cursor.next() {
        let token = match item {
            ScanItem::Token(token) => LexedToken {
                kind: syntax_kind(token.kind, token.text),
                range: token.range,
            },
            ScanItem::Trivia(trivia) => LexedToken {
                kind: match trivia.kind {
                    TriviaKind::Space => SyntaxKind::Whitespace,
                    TriviaKind::Newline { .. } => SyntaxKind::Newline,
                },
                range: trivia.range,
            },
        };
        tokens.push(token);
    }

    tokens
}

fn syntax_kind(kind: TokenKind, text: &str) -> SyntaxKind {
    match kind {
        TokenKind::Identifier if text == "my" => SyntaxKind::MyKw,
        TokenKind::Identifier => SyntaxKind::Identifier,
        TokenKind::Keyword(HeaderKeyword::Use) => SyntaxKind::UseKw,
        TokenKind::Keyword(HeaderKeyword::Infix) => SyntaxKind::InfixKw,
        TokenKind::Number => SyntaxKind::Integer,
        TokenKind::Dot => SyntaxKind::Dot,
        TokenKind::ColonColon => SyntaxKind::ColonColon,
        TokenKind::Open(Delimiter::Parenthesis) => SyntaxKind::LParen,
        TokenKind::Close(Delimiter::Parenthesis) => SyntaxKind::RParen,
        TokenKind::Equals => SyntaxKind::Equals,
        TokenKind::Symbol => SyntaxKind::Operator,
        TokenKind::Open(Delimiter::Brace | Delimiter::Bracket)
        | TokenKind::Close(Delimiter::Brace | Delimiter::Bracket) => SyntaxKind::Unknown,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        BindingPower as HeaderBindingPower, BindingPowers, HeaderOperator, Visibility,
        operator::{
            BindingPower, OperatorDeclaration, OperatorFixities, compile_full_parse_operators,
        },
    };

    #[test]
    fn parse_file_keeps_the_first_local_fixity_and_reports_the_rejected_site() {
        let source: Arc<SourceText> = Arc::from(
            "infix (<+>) 40 41 = left\ninfix (<+>) 42 43 = right\n",
        );
        let header = Arc::new(crate::scan_header(Arc::clone(&source)));

        assert_eq!(header.operators().len(), 2);
        let parsed = parse_file(
            Arc::clone(&source),
            Arc::clone(&header),
            Arc::new(SyntaxEnvironment::empty()),
        );

        assert_eq!(parsed.green().to_string(), source.as_ref());
        let [diagnostic] = parsed.diagnostics() else {
            panic!("the duplicate fixity must be diagnosed");
        };
        assert_eq!(diagnostic.primary(), header.operators()[1].range());
        let SyntaxDiagnosticCause::ConflictingOperatorFixity(conflict) = diagnostic.cause() else {
            panic!("operator construction must not masquerade as CST recovery");
        };
        assert_eq!(conflict.spelling(), "<+>");
        assert_eq!(conflict.fixity(), OperatorFixity::Infix);
        assert_eq!(conflict.first_origin(), OperatorOrigin::Local);
        assert_eq!(conflict.second_origin(), OperatorOrigin::Local);
        assert_eq!(conflict.first_range(), header.operators()[0].range());
        assert_eq!(conflict.second_range(), header.operators()[1].range());
    }

    #[test]
    fn recovery_diagnostic_keeps_the_committed_record_distinct_from_construction() {
        use crate::session::{
            ExpectationSources, ExpectedSyntax, GrammarRole, ParseLocal, RecoveryKind,
            RecoverySiteKey, StatementRole, SyntaxExpectation,
        };

        let mut local = ParseLocal::new();
        for _ in 0..9 {
            local.next_diagnostic_id();
        }
        let record = CommittedRecoveryRecord::new(
            &mut local,
            RecoverySiteKey {
                role: GrammarRole::Statement(StatementRole::Starter),
                range: 4..4,
            },
            RecoveryKind::Missing,
            Arc::from([]),
            Arc::from([SyntaxExpectation {
                role: GrammarRole::Statement(StatementRole::Starter),
                expected: ExpectedSyntax::Expression,
                range: 4..4,
                sources: ExpectationSources::COMMITTED_RECOVERY_RULE,
            }]),
            0,
        );
        let diagnostic = SyntaxDiagnostic::recovery(record.clone());

        assert_eq!(diagnostic.id(), 9);
        assert_eq!(diagnostic.primary(), &(4..4));
        let SyntaxDiagnosticCause::Recovery(recovery) = diagnostic.cause() else {
            panic!("a recovery record must not be a construction conflict");
        };
        assert_eq!(recovery.record(), &record);
    }

    #[test]
    fn imported_environment_rejects_a_full_table_with_local_sites() {
        let operators = Arc::new(
            OperatorTable::from_declarations([OperatorDeclaration::at_range(
                "+",
                OperatorFixities::new().with_prefix(crate::operator::BindingPower::scalar(70)),
                4..12,
            )])
            .expect("local full table should build"),
        );

        let error =
            SyntaxEnvironment::from_imported(SyntaxEnvironmentKey(1), operators, Arc::from([]))
                .expect_err("a different file's full table must not become imported input");

        assert_eq!(
            error,
            SyntaxEnvironmentBuildError::ImportedTableContainsLocalOrigin {
                spelling: "+".into(),
                fixity: OperatorFixity::Prefix,
                range: 4..12,
            }
        );
    }

    #[test]
    fn imported_environment_rejects_an_out_of_range_dependency_slot() {
        let missing_dependency = SyntaxDependencySlot::from_index(1).expect("slot fits");
        let operators = Arc::new(
            OperatorTable::from_declarations([OperatorDeclaration::imported_at_range(
                "+",
                OperatorFixities::new().with_prefix(crate::operator::BindingPower::scalar(70)),
                missing_dependency,
                4..12,
            )])
            .expect("imported table should build"),
        );
        let provenance = Arc::from([SyntaxDependencyProvenance::new(
            Arc::from("dependency"),
            SourceRevision::UNTRACKED,
        )]);

        let error =
            SyntaxEnvironment::from_imported(SyntaxEnvironmentKey(1), operators, provenance)
                .expect_err("missing dependency provenance must be rejected");

        assert_eq!(
            error,
            SyntaxEnvironmentBuildError::MissingDependencyProvenance {
                spelling: "+".into(),
                fixity: OperatorFixity::Prefix,
                dependency: missing_dependency,
                range: 4..12,
            }
        );
    }

    #[test]
    fn imported_environment_keeps_received_arcs_and_unused_provenance() {
        let operators = Arc::new(OperatorTable::empty());
        let provenance = Arc::from([SyntaxDependencyProvenance::new(
            Arc::from("dependency without operators"),
            SourceRevision::UNTRACKED,
        )]);

        let environment = SyntaxEnvironment::from_imported(
            SyntaxEnvironmentKey(1),
            Arc::clone(&operators),
            Arc::clone(&provenance),
        )
        .expect("unused dependency provenance is valid");

        assert!(Arc::ptr_eq(&operators, &environment.operators));
        assert!(Arc::ptr_eq(&provenance, &environment.provenance));
        assert_eq!(
            environment
                .dependency(SyntaxDependencySlot::from_index(0).expect("first slot fits"))
                .expect("stored dependency")
                .module_label(),
            "dependency without operators"
        );
    }

    #[test]
    fn full_parse_merge_does_not_mutate_environment_operator_sites() {
        let dependency = SyntaxDependencySlot::from_index(0).expect("first slot fits");
        let operators = Arc::new(
            OperatorTable::from_declarations([OperatorDeclaration::imported_at_range(
                "+",
                OperatorFixities::new().with_prefix(BindingPower::scalar(70)),
                dependency,
                4..12,
            )])
            .expect("imported table should build"),
        );
        let provenance = Arc::from([SyntaxDependencyProvenance::new(
            Arc::from("dependency"),
            SourceRevision::UNTRACKED,
        )]);
        let environment = SyntaxEnvironment::from_imported(
            SyntaxEnvironmentKey(1),
            Arc::clone(&operators),
            provenance,
        )
        .expect("validated imported environment");
        let (_, before_sites) = environment
            .operators()
            .entries_with_sites()
            .next()
            .expect("imported entry");
        let before_prefix = before_sites
            .site(OperatorFixity::Prefix)
            .cloned()
            .expect("imported prefix site");
        let local = [HeaderOperator::new(
            20..36,
            "+".to_owned(),
            OperatorFixity::Infix,
            Visibility::Private,
            false,
            BindingPowers::infix(
                HeaderBindingPower::from_components([40]),
                HeaderBindingPower::from_components([41]),
            ),
        )];

        let merged = compile_full_parse_operators(environment.operators(), &local)
            .expect("merge builds a separate full parse table");

        assert!(Arc::ptr_eq(&operators, &environment.operators));
        let (_, after_sites) = environment
            .operators()
            .entries_with_sites()
            .next()
            .expect("imported entry remains unchanged");
        assert_eq!(
            after_sites.site(OperatorFixity::Prefix),
            Some(&before_prefix)
        );
        assert!(after_sites.site(OperatorFixity::Infix).is_none());
        assert!(
            merged
                .get("+")
                .expect("merged entry")
                .fixities()
                .infix()
                .is_some()
        );
    }
}
