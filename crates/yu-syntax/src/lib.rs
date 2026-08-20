//! Syntax boundary for Yulang3.

use std::{ops::Range, sync::Arc};

#[allow(dead_code)]
mod input;
mod grammar;
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

pub use parse::{
    OperatorTable, ParsedFile, SourceRevision, SyntaxDependencyProvenance, SyntaxDiagnostic,
    SyntaxEnvironment, SyntaxEnvironmentKey, parse_file,
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
    path: Vec<String>,
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
        &self.path
    }

    pub fn visibility(&self) -> Visibility {
        self.visibility
    }

    pub fn alias(&self) -> Option<&str> {
        self.alias.as_deref()
    }
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
    Public,
}

/// A dynamic operator signature discovered in the header.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct HeaderOperator {
    range: Range<usize>,
    name: String,
    fixity: OperatorFixity,
    visibility: Visibility,
    binding_power: BindingPower,
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

    pub fn binding_power(&self) -> BindingPower {
        self.binding_power
    }
}

/// Canonical operator fixity.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum OperatorFixity {
    Infix,
}

/// Binding-power sides applicable to an operator signature.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct BindingPower {
    left: Option<u16>,
    right: Option<u16>,
}

impl BindingPower {
    pub fn left(self) -> Option<u16> {
        self.left
    }

    pub fn right(self) -> Option<u16> {
        self.right
    }
}

/// Discover leading plain imports and infix operator signatures.
pub fn scan_header(source: Arc<SourceText>) -> HeaderInfo {
    let source = source.as_ref();
    let mut cursor = HeaderCursor::new(source);
    let mut imports = Vec::new();
    let mut operators = Vec::new();
    let mut coverage_end = 0;

    while cursor.is_at_header_start() {
        let declaration_start = cursor.position();
        let Some(ScanItem::Token(starter)) = cursor.next() else {
            break;
        };

        let declaration = match starter.kind {
            TokenKind::Keyword(HeaderKeyword::Use) => {
                scan_plain_use(&mut cursor, declaration_start).map(HeaderDeclaration::Import)
            }
            TokenKind::Keyword(HeaderKeyword::Infix) => {
                scan_infix_operator(&mut cursor, declaration_start).map(HeaderDeclaration::Operator)
            }
            _ => None,
        };

        match declaration {
            Some(HeaderDeclaration::Import(import)) => imports.push(import),
            Some(HeaderDeclaration::Operator(operator)) => operators.push(operator),
            None => break,
        }

        coverage_end = cursor.position();
    }

    let stop = if coverage_end == source.len() {
        HeaderStop::Eof
    } else {
        HeaderStop::FirstNonHeader
    };

    HeaderInfo {
        coverage: HeaderCoverage {
            range: 0..coverage_end,
            stop,
        },
        imports: imports.into(),
        operators: operators.into(),
    }
}

enum HeaderDeclaration {
    Import(HeaderImport),
    Operator(HeaderOperator),
}

fn scan_plain_use(cursor: &mut HeaderCursor<'_>, range_start: usize) -> Option<HeaderImport> {
    cursor.consume_exact_space()?;
    let first_component = cursor.consume_path_component()?;
    let mut range_end = first_component.range.end;
    let mut path = vec![first_component.text.to_owned()];

    loop {
        match cursor.next() {
            Some(ScanItem::Token(Token {
                kind: TokenKind::ColonColon,
                ..
            })) => {
                let component = cursor.consume_path_component()?;
                range_end = component.range.end;
                path.push(component.text.to_owned());
            }
            Some(ScanItem::Trivia(Trivia {
                kind: TriviaKind::Newline { indentation },
                ..
            })) => {
                debug_assert_eq!(cursor.indentation(), indentation);
                break;
            }
            None => break,
            _ => return None,
        }
    }

    Some(HeaderImport {
        range: range_start..range_end,
        form: HeaderImportForm::Plain,
        path,
        visibility: Visibility::Private,
        alias: None,
    })
}

fn scan_infix_operator(
    cursor: &mut HeaderCursor<'_>,
    range_start: usize,
) -> Option<HeaderOperator> {
    cursor.consume_exact_space()?;
    cursor.consume_token(TokenKind::Open(Delimiter::Parenthesis))?;
    let parenthesis_depth = cursor.delimiter_depth();
    let name = cursor.consume_operator_name(parenthesis_depth)?.to_owned();
    cursor.consume_spaces()?;
    let left = cursor.consume_u16()?;
    cursor.consume_spaces()?;
    let right = cursor.consume_u16()?;
    cursor.consume_spaces()?;
    let equals = cursor.consume_token(TokenKind::Equals)?;
    cursor.consume_line_remainder();

    Some(HeaderOperator {
        range: range_start..equals.range.end,
        name,
        fixity: OperatorFixity::Infix,
        visibility: Visibility::Private,
        binding_power: BindingPower {
            left: Some(left),
            right: Some(right),
        },
    })
}

/// Minimal lexical state shared by header declaration discovery.
///
/// Trivia stays separate from content tokens, while delimiter and indentation
/// state remain available for later recovery and opaque-scan policies.
struct HeaderCursor<'source> {
    source: &'source str,
    position: usize,
    line_start: usize,
    indentation: usize,
    delimiters: Vec<Delimiter>,
}

impl<'source> HeaderCursor<'source> {
    fn new(source: &'source str) -> Self {
        Self {
            source,
            position: 0,
            line_start: 0,
            indentation: indentation_at(source, 0),
            delimiters: Vec::new(),
        }
    }

    fn position(&self) -> usize {
        self.position
    }

    fn indentation(&self) -> usize {
        self.indentation
    }

    fn delimiter_depth(&self) -> usize {
        self.delimiters.len()
    }

    fn is_at_header_start(&self) -> bool {
        self.position == self.line_start && self.indentation == 0 && self.delimiters.is_empty()
    }

    fn next(&mut self) -> Option<ScanItem<'source>> {
        if self.position == self.source.len() {
            return None;
        }

        let start = self.position;
        let remainder = &self.source[start..];

        if remainder.starts_with([' ', '\t']) {
            self.position += remainder
                .bytes()
                .take_while(|byte| matches!(byte, b' ' | b'\t'))
                .count();
            return Some(ScanItem::Trivia(Trivia {
                kind: TriviaKind::Space,
                range: start..self.position,
            }));
        }

        if let Some(newline_len) = newline_len(remainder) {
            self.position += newline_len;
            self.line_start = self.position;
            self.indentation = indentation_at(self.source, self.position);
            return Some(ScanItem::Trivia(Trivia {
                kind: TriviaKind::Newline {
                    indentation: self.indentation,
                },
                range: start..self.position,
            }));
        }

        let (kind, end) = scan_token(self.source, start);
        self.position = end;
        self.update_delimiters(kind);

        Some(ScanItem::Token(Token {
            kind,
            text: &self.source[start..end],
            range: start..end,
        }))
    }

    fn consume_exact_space(&mut self) -> Option<()> {
        let ScanItem::Trivia(trivia) = self.next()? else {
            return None;
        };

        (trivia.kind == TriviaKind::Space && self.source[trivia.range] == *" ").then_some(())
    }

    fn consume_spaces(&mut self) -> Option<()> {
        let ScanItem::Trivia(trivia) = self.next()? else {
            return None;
        };

        (trivia.kind == TriviaKind::Space
            && self.source[trivia.range].bytes().all(|byte| byte == b' '))
        .then_some(())
    }

    fn consume_path_component(&mut self) -> Option<Token<'source>> {
        let ScanItem::Token(token) = self.next()? else {
            return None;
        };

        token.kind.is_word().then_some(token)
    }

    fn consume_token(&mut self, expected: TokenKind) -> Option<Token<'source>> {
        let ScanItem::Token(token) = self.next()? else {
            return None;
        };

        (token.kind == expected).then_some(token)
    }

    fn consume_operator_name(&mut self, parenthesis_depth: usize) -> Option<&'source str> {
        let name_start = self.position;

        loop {
            let ScanItem::Token(token) = self.next()? else {
                return None;
            };

            if token.kind == TokenKind::Close(Delimiter::Parenthesis)
                && self.delimiter_depth() + 1 == parenthesis_depth
            {
                return (name_start < token.range.start)
                    .then_some(&self.source[name_start..token.range.start]);
            }
        }
    }

    fn consume_u16(&mut self) -> Option<u16> {
        let token = self.consume_token(TokenKind::Number)?;
        token.text.parse().ok()
    }

    fn consume_line_remainder(&mut self) {
        // Operator bodies remain single-line in this slice. Delimiter state is
        // still updated so a later balanced opaque scan can extend this point.
        while let Some(item) = self.next() {
            if let ScanItem::Trivia(Trivia {
                kind: TriviaKind::Newline { indentation },
                ..
            }) = item
            {
                debug_assert_eq!(self.indentation, indentation);
                break;
            }
        }
    }

    fn update_delimiters(&mut self, token: TokenKind) {
        match token {
            TokenKind::Open(delimiter) => self.delimiters.push(delimiter),
            TokenKind::Close(delimiter) if self.delimiters.last() == Some(&delimiter) => {
                self.delimiters.pop();
            }
            _ => {}
        }
    }
}

enum ScanItem<'source> {
    Token(Token<'source>),
    Trivia(Trivia),
}

struct Token<'source> {
    kind: TokenKind,
    text: &'source str,
    range: Range<usize>,
}

struct Trivia {
    kind: TriviaKind,
    range: Range<usize>,
}

#[derive(Clone, Copy, Eq, PartialEq)]
enum TriviaKind {
    Space,
    Newline { indentation: usize },
}

#[derive(Clone, Copy, Eq, PartialEq)]
enum TokenKind {
    Identifier,
    Keyword(HeaderKeyword),
    Number,
    Dot,
    ColonColon,
    Open(Delimiter),
    Close(Delimiter),
    Equals,
    Symbol,
}

impl TokenKind {
    fn is_word(self) -> bool {
        matches!(self, Self::Identifier | Self::Keyword(_))
    }
}

#[derive(Clone, Copy, Eq, PartialEq)]
enum HeaderKeyword {
    Use,
    Infix,
}

#[derive(Clone, Copy, Eq, PartialEq)]
enum Delimiter {
    Parenthesis,
    Brace,
    Bracket,
}

fn scan_token(source: &str, start: usize) -> (TokenKind, usize) {
    let remainder = &source[start..];
    let first = remainder.as_bytes()[0];

    if first.is_ascii_alphabetic() || first == b'_' {
        let length = remainder
            .bytes()
            .take_while(|byte| byte.is_ascii_alphanumeric() || *byte == b'_')
            .count();
        let end = start + length;
        let kind = match &source[start..end] {
            "use" => TokenKind::Keyword(HeaderKeyword::Use),
            "infix" => TokenKind::Keyword(HeaderKeyword::Infix),
            _ => TokenKind::Identifier,
        };
        return (kind, end);
    }

    if first.is_ascii_digit() {
        let length = remainder.bytes().take_while(u8::is_ascii_digit).count();
        return (TokenKind::Number, start + length);
    }

    if remainder.starts_with("::") {
        return (TokenKind::ColonColon, start + 2);
    }

    let single_byte = match first {
        b'.' => Some(TokenKind::Dot),
        b'(' => Some(TokenKind::Open(Delimiter::Parenthesis)),
        b')' => Some(TokenKind::Close(Delimiter::Parenthesis)),
        b'{' => Some(TokenKind::Open(Delimiter::Brace)),
        b'}' => Some(TokenKind::Close(Delimiter::Brace)),
        b'[' => Some(TokenKind::Open(Delimiter::Bracket)),
        b']' => Some(TokenKind::Close(Delimiter::Bracket)),
        b'=' => Some(TokenKind::Equals),
        _ => None,
    };

    if let Some(kind) = single_byte {
        return (kind, start + 1);
    }

    (TokenKind::Symbol, scan_symbol_end(source, start))
}

fn scan_symbol_end(source: &str, start: usize) -> usize {
    let mut end = start;

    for (relative, character) in source[start..].char_indices() {
        let position = start + relative;
        if position > start && starts_distinct_item(source, position, character) {
            break;
        }
        end = position + character.len_utf8();
    }

    end
}

fn starts_distinct_item(source: &str, position: usize, character: char) -> bool {
    character.is_ascii_alphanumeric()
        || matches!(
            character,
            '_' | ' ' | '\t' | '\r' | '\n' | '.' | '(' | ')' | '{' | '}' | '[' | ']' | '='
        )
        || source[position..].starts_with("::")
}

fn newline_len(source: &str) -> Option<usize> {
    if source.starts_with("\r\n") {
        Some(2)
    } else if source.starts_with(['\r', '\n']) {
        Some(1)
    } else {
        None
    }
}

fn indentation_at(source: &str, position: usize) -> usize {
    source[position..]
        .bytes()
        .take_while(|byte| matches!(byte, b' ' | b'\t'))
        .count()
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
        assert_eq!(operator.binding_power().left(), Some(50));
        assert_eq!(operator.binding_power().right(), Some(51));
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
                text.parse::<u16>()
                    .expect("fixture binding power must fit u16")
            })
            .collect::<Vec<_>>();
        assert_eq!(
            binding_powers,
            [
                operator.binding_power().left().unwrap(),
                operator.binding_power().right().unwrap(),
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
