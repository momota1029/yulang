use std::collections::HashMap;
use std::path::{Path, PathBuf};
use std::sync::Mutex;

use tower_lsp::lsp_types::*;
use tower_lsp::{Client, LanguageServer, LspService, Server};
use yulang_editor::semantic_tokens;

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
                source: Some("yulang".to_string()),
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
            source: Some("yulang".to_string()),
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
            token_types: semantic_tokens::TOKEN_TYPES
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
                name: "yulang server".to_string(),
                version: Some(env!("CARGO_PKG_VERSION").to_string()),
            }),
        })
    }

    async fn initialized(&self, _: InitializedParams) {
        self.client
            .log_message(MessageType::INFO, "yulang server initialized")
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
    semantic_tokens::compute(source)
        .chunks_exact(5)
        .map(|chunk| SemanticToken {
            delta_line: chunk[0],
            delta_start: chunk[1],
            length: chunk[2],
            token_type: chunk[3],
            token_modifiers_bitset: chunk[4],
        })
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn semantic_tokens_include_keyword_number_and_string() {
        let tokens = semantic_tokens_for_source("my x = \"hi\"\n1\n");
        let keyword = token_type_index("keyword");
        let string = token_type_index("string");
        let number = token_type_index("number");

        assert!(
            tokens.iter().any(|token| token.token_type == keyword),
            "{tokens:?}"
        );
        assert!(
            tokens.iter().any(|token| token.token_type == string),
            "{tokens:?}"
        );
        assert!(
            tokens.iter().any(|token| token.token_type == number),
            "{tokens:?}"
        );
    }

    fn token_type_index(name: &str) -> u32 {
        semantic_tokens::TOKEN_TYPES
            .iter()
            .position(|token| *token == name)
            .expect("semantic token type") as u32
    }
}
