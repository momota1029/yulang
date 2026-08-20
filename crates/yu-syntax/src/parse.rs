use std::{ops::Range, sync::Arc};

use rowan::{GreenNode, GreenNodeBuilder};

use crate::{
    Delimiter, HeaderCursor, HeaderInfo, HeaderKeyword, ScanItem, SourceText, TokenKind,
    TriviaKind, syntax_kind::SyntaxKind,
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
            operators: Arc::new(OperatorTable),
            provenance: Arc::from([]),
        }
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
    let green = FullCstBuilder::new(source.as_ref(), header.as_ref()).build();

    ParsedFile {
        source,
        revision: SourceRevision::UNTRACKED,
        header,
        syntax_environment: syntax.key(),
        green,
        diagnostics: Arc::from([]),
    }
}

/// Opaque identity of the syntax inputs selected for a parse.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct SyntaxEnvironmentKey(u64);

impl SyntaxEnvironmentKey {
    pub const EMPTY: Self = Self(0);
}

/// Imported operator table selected by syntax planning.
#[derive(Debug, Default)]
pub struct OperatorTable;

/// Provenance for one syntax dependency selected by syntax planning.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SyntaxDependencyProvenance {
    _private: (),
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
    _private: (),
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
