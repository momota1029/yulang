use std::collections::HashMap;
use std::path::{Path, PathBuf};
use std::sync::Mutex;

use rowan::{NodeOrToken, SyntaxNode};
use tower_lsp::lsp_types::*;
use tower_lsp::{Client, LanguageServer, LspService, Server};
use yulang_parser::lex::SyntaxKind;
use yulang_parser::sink::YulangLanguage;

const TOKEN_TYPES: &[&str] = &[
    "keyword",   // 0
    "string",    // 1
    "number",    // 2
    "comment",   // 3
    "operator",  // 4
    "delimiter", // 5
    "type",      // 6
];

const KEYWORD: u32 = 0;
const STRING: u32 = 1;
const NUMBER: u32 = 2;
const COMMENT: u32 = 3;
const OPERATOR: u32 = 4;
const DELIMITER: u32 = 5;

struct Backend {
    client: Client,
    std_root: Option<PathBuf>,
    documents: Mutex<HashMap<Url, String>>,
    analysis_versions: Mutex<HashMap<Url, u64>>,
}

impl Backend {
    async fn analyze(&self, uri: Url) {
        let version = self.bump_analysis_version(&uri);
        let path = match uri.to_file_path() {
            Ok(path) => path,
            Err(_) => return,
        };
        let source = self
            .documents
            .lock()
            .unwrap()
            .get(&uri)
            .cloned()
            .or_else(|| std::fs::read_to_string(&path).ok());
        let Some(source) = source else {
            return;
        };
        let options = crate::StdSourceOptions {
            std_root: self.std_root.clone(),
        };
        let diagnostics =
            tokio::task::spawn_blocking(move || diagnostics_for_source(&path, source, &options))
                .await
                .unwrap_or_default();
        if !self.is_current_analysis_version(&uri, version) {
            return;
        }
        self.client
            .publish_diagnostics(uri, diagnostics, None)
            .await;
    }

    fn bump_analysis_version(&self, uri: &Url) -> u64 {
        let mut versions = self.analysis_versions.lock().unwrap();
        let next = versions.get(uri).copied().unwrap_or(0).wrapping_add(1);
        versions.insert(uri.clone(), next);
        next
    }

    fn cancel_analysis(&self, uri: &Url) {
        self.bump_analysis_version(uri);
    }

    fn is_current_analysis_version(&self, uri: &Url, version: u64) -> bool {
        self.analysis_versions
            .lock()
            .unwrap()
            .get(uri)
            .copied()
            .unwrap_or(0)
            == version
    }

    fn document_source(&self, uri: &Url) -> Option<String> {
        self.documents
            .lock()
            .unwrap()
            .get(uri)
            .cloned()
            .or_else(|| {
                uri.to_file_path()
                    .ok()
                    .and_then(|path| std::fs::read_to_string(path).ok())
            })
    }
}

fn diagnostics_for_source(
    path: &Path,
    source: String,
    options: &crate::StdSourceOptions,
) -> Vec<Diagnostic> {
    match crate::analyze_entry_source_with_std_options(path, source, options) {
        Ok(output) => output
            .diagnostics
            .into_iter()
            .map(|diagnostic| Diagnostic {
                range: Range::default(),
                severity: Some(DiagnosticSeverity::ERROR),
                source: Some("yulang2".to_string()),
                message: match diagnostic.label {
                    Some(label) => format!("{label}: {}", diagnostic.message),
                    None => diagnostic.message,
                },
                ..Default::default()
            })
            .collect(),
        Err(error) => vec![Diagnostic {
            range: Range::default(),
            severity: Some(DiagnosticSeverity::ERROR),
            source: Some("yulang2".to_string()),
            message: error.to_string(),
            ..Default::default()
        }],
    }
}

#[tower_lsp::async_trait]
impl LanguageServer for Backend {
    async fn initialize(
        &self,
        _params: InitializeParams,
    ) -> tower_lsp::jsonrpc::Result<InitializeResult> {
        let legend = SemanticTokensLegend {
            token_types: TOKEN_TYPES
                .iter()
                .map(|token| SemanticTokenType::new(*token))
                .collect(),
            token_modifiers: vec![],
        };

        Ok(InitializeResult {
            capabilities: ServerCapabilities {
                text_document_sync: Some(TextDocumentSyncCapability::Kind(
                    TextDocumentSyncKind::FULL,
                )),
                semantic_tokens_provider: Some(
                    SemanticTokensServerCapabilities::SemanticTokensOptions(
                        SemanticTokensOptions {
                            legend,
                            full: Some(SemanticTokensFullOptions::Bool(true)),
                            range: None,
                            work_done_progress_options: Default::default(),
                        },
                    ),
                ),
                ..Default::default()
            },
            server_info: Some(ServerInfo {
                name: "yulang2 server".to_string(),
                version: Some(env!("CARGO_PKG_VERSION").to_string()),
            }),
        })
    }

    async fn initialized(&self, _: InitializedParams) {
        self.client
            .log_message(MessageType::INFO, "yulang2 server initialized")
            .await;
    }

    async fn shutdown(&self) -> tower_lsp::jsonrpc::Result<()> {
        Ok(())
    }

    async fn did_open(&self, params: DidOpenTextDocumentParams) {
        self.documents
            .lock()
            .unwrap()
            .insert(params.text_document.uri.clone(), params.text_document.text);
        self.analyze(params.text_document.uri).await;
    }

    async fn did_change(&self, params: DidChangeTextDocumentParams) {
        if let Some(change) = params.content_changes.into_iter().last() {
            self.documents
                .lock()
                .unwrap()
                .insert(params.text_document.uri.clone(), change.text);
        }
        self.analyze(params.text_document.uri).await;
    }

    async fn did_save(&self, params: DidSaveTextDocumentParams) {
        if let Some(text) = params.text {
            self.documents
                .lock()
                .unwrap()
                .insert(params.text_document.uri.clone(), text);
        }
        self.analyze(params.text_document.uri).await;
    }

    async fn did_close(&self, params: DidCloseTextDocumentParams) {
        self.documents
            .lock()
            .unwrap()
            .remove(&params.text_document.uri);
        self.cancel_analysis(&params.text_document.uri);
        self.client
            .publish_diagnostics(params.text_document.uri, Vec::new(), None)
            .await;
    }

    async fn semantic_tokens_full(
        &self,
        params: SemanticTokensParams,
    ) -> tower_lsp::jsonrpc::Result<Option<SemanticTokensResult>> {
        let source = self.document_source(&params.text_document.uri);
        let data = source
            .as_deref()
            .map(semantic_tokens_for_source)
            .unwrap_or_default();
        Ok(Some(SemanticTokensResult::Tokens(SemanticTokens {
            result_id: None,
            data,
        })))
    }
}

pub async fn serve(std_root: Option<PathBuf>) {
    let stdin = tokio::io::stdin();
    let stdout = tokio::io::stdout();
    let (service, socket) = LspService::new(|client| Backend {
        client,
        std_root,
        documents: Mutex::new(HashMap::new()),
        analysis_versions: Mutex::new(HashMap::new()),
    });
    Server::new(stdin, stdout, socket).serve(service).await;
}

pub fn run_blocking(std_root: Option<PathBuf>) {
    let runtime = tokio::runtime::Builder::new_multi_thread()
        .enable_all()
        .build()
        .expect("failed to create tokio runtime for Yulang2 language server");
    runtime.block_on(serve(std_root));
}

fn semantic_tokens_for_source(source: &str) -> Vec<SemanticToken> {
    let root = SyntaxNode::<YulangLanguage>::new_root(yulang_parser::parse_module_to_green(source));
    let line_starts = line_starts(source);
    let mut raw = Vec::new();

    for item in root.descendants_with_tokens() {
        let NodeOrToken::Token(token) = item else {
            continue;
        };
        let Some(token_type) = token_type(token.kind()) else {
            continue;
        };
        let start = usize::from(token.text_range().start());
        let (line, col) = byte_to_pos(source, &line_starts, start);
        let length = token.text().encode_utf16().count() as u32;
        if length > 0 {
            raw.push((line, col, length, token_type));
        }
    }

    raw.sort_unstable();
    raw.dedup();
    encode_semantic_tokens(raw)
}

fn token_type(kind: SyntaxKind) -> Option<u32> {
    match kind {
        SyntaxKind::LineComment
        | SyntaxKind::BlockComment
        | SyntaxKind::BlockCommentStart
        | SyntaxKind::BlockCommentText
        | SyntaxKind::BlockCommentEnd => Some(COMMENT),
        SyntaxKind::StringStart
        | SyntaxKind::StringEnd
        | SyntaxKind::StringText
        | SyntaxKind::StringEscapeLead
        | SyntaxKind::StringEscapeSimple
        | SyntaxKind::StringEscapeUnicodeStart
        | SyntaxKind::StringEscapeUnicodeHex
        | SyntaxKind::StringEscapeUnicodeEnd
        | SyntaxKind::StringInterpPercent
        | SyntaxKind::StringInterpFormatText
        | SyntaxKind::StringInterpOpenBrace
        | SyntaxKind::StringInterpCloseBrace => Some(STRING),
        SyntaxKind::Number => Some(NUMBER),
        SyntaxKind::Do
        | SyntaxKind::If
        | SyntaxKind::Else
        | SyntaxKind::Elsif
        | SyntaxKind::Case
        | SyntaxKind::Catch
        | SyntaxKind::My
        | SyntaxKind::Our
        | SyntaxKind::Pub
        | SyntaxKind::Use
        | SyntaxKind::Type
        | SyntaxKind::Struct
        | SyntaxKind::Enum
        | SyntaxKind::Role
        | SyntaxKind::Impl
        | SyntaxKind::Act
        | SyntaxKind::Mod
        | SyntaxKind::As
        | SyntaxKind::For
        | SyntaxKind::In
        | SyntaxKind::With
        | SyntaxKind::Where
        | SyntaxKind::Via
        | SyntaxKind::Mark
        | SyntaxKind::Rule
        | SyntaxKind::Lazy => Some(KEYWORD),
        SyntaxKind::Prefix
        | SyntaxKind::Infix
        | SyntaxKind::Suffix
        | SyntaxKind::Nullfix
        | SyntaxKind::Arrow
        | SyntaxKind::Pipe
        | SyntaxKind::Backslash
        | SyntaxKind::DotDot
        | SyntaxKind::Tilde
        | SyntaxKind::RuleQuantStar
        | SyntaxKind::RuleQuantStarLazy
        | SyntaxKind::RuleQuantPlus
        | SyntaxKind::RuleQuantPlusLazy
        | SyntaxKind::RuleQuantOpt => Some(OPERATOR),
        SyntaxKind::Colon | SyntaxKind::ColonColon | SyntaxKind::Equal => Some(DELIMITER),
        _ => None,
    }
}

fn encode_semantic_tokens(raw: Vec<(u32, u32, u32, u32)>) -> Vec<SemanticToken> {
    let mut encoded = Vec::with_capacity(raw.len());
    let mut last_line = 0;
    let mut last_col = 0;
    for (line, col, length, token_type) in raw {
        let delta_line = line - last_line;
        let delta_start = if delta_line == 0 { col - last_col } else { col };
        encoded.push(SemanticToken {
            delta_line,
            delta_start,
            length,
            token_type,
            token_modifiers_bitset: 0,
        });
        last_line = line;
        last_col = col;
    }
    encoded
}

fn line_starts(source: &str) -> Vec<usize> {
    let mut starts = vec![0];
    for (idx, ch) in source.char_indices() {
        if ch == '\n' {
            starts.push(idx + 1);
        }
    }
    starts
}

fn byte_to_pos(source: &str, line_starts: &[usize], byte: usize) -> (u32, u32) {
    let line = line_starts
        .partition_point(|line_start| *line_start <= byte)
        .saturating_sub(1);
    let col = source_col_utf16(source, line_starts, line, byte);
    (line as u32, col)
}

fn source_col_utf16(source: &str, line_starts: &[usize], line: usize, byte: usize) -> u32 {
    let line_start = line_starts.get(line).copied().unwrap_or(0);
    source[line_start..byte].encode_utf16().count() as u32
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn semantic_tokens_include_keyword_number_and_string() {
        let tokens = semantic_tokens_for_source("my x = \"hi\"\n1\n");

        assert!(
            tokens.iter().any(|token| token.token_type == KEYWORD),
            "{tokens:?}"
        );
        assert!(
            tokens.iter().any(|token| token.token_type == STRING),
            "{tokens:?}"
        );
        assert!(
            tokens.iter().any(|token| token.token_type == NUMBER),
            "{tokens:?}"
        );
    }
}
