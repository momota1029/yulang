use std::collections::HashMap;
use std::path::{Path, PathBuf};
use std::sync::Mutex;

use tower_lsp::lsp_types::*;
use tower_lsp::{Client, LanguageServer, LspService, Server};
use yulang_editor::semantic_tokens;

use crate::SourceRange;

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
    let document_source = source.clone();
    match crate::analyze_entry_source_with_std_options(path, source, options) {
        Ok(output) => output
            .diagnostics
            .into_iter()
            .map(|diagnostic| Diagnostic {
                range: diagnostic
                    .range
                    .map(|range| lsp_range_for_loaded_root_range(&document_source, range))
                    .unwrap_or_default(),
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

fn lsp_range_for_loaded_root_range(source: &str, range: SourceRange) -> Range {
    source_range_to_lsp_range(source, subtract_implicit_prelude_range(range))
}

fn subtract_implicit_prelude_range(range: SourceRange) -> SourceRange {
    let offset = crate::source::IMPLICIT_PRELUDE_IMPORT.len()
        + crate::source::IMPLICIT_STD_MODULE_DECL.len();
    if range.start < offset {
        return range;
    }
    SourceRange {
        start: range.start - offset,
        end: range.end.saturating_sub(offset),
    }
}

fn source_range_to_lsp_range(source: &str, range: SourceRange) -> Range {
    let start = clamp_to_char_boundary(source, range.start.min(source.len()));
    let end = clamp_to_char_boundary(source, range.end.min(source.len())).max(start);
    let line_starts = compute_line_starts(source);
    Range {
        start: byte_offset_to_position(source, &line_starts, start),
        end: byte_offset_to_position(source, &line_starts, end),
    }
}

fn compute_line_starts(source: &str) -> Vec<usize> {
    let mut starts = vec![0];
    for (index, byte) in source.bytes().enumerate() {
        if byte == b'\n' {
            starts.push(index + 1);
        }
    }
    starts
}

fn byte_offset_to_position(source: &str, line_starts: &[usize], offset: usize) -> Position {
    let line = line_starts
        .partition_point(|start| *start <= offset)
        .saturating_sub(1);
    let line_start = line_starts.get(line).copied().unwrap_or(0);
    Position {
        line: line as u32,
        character: source[line_start..offset].encode_utf16().count() as u32,
    }
}

fn clamp_to_char_boundary(source: &str, mut offset: usize) -> usize {
    while offset > 0 && !source.is_char_boundary(offset) {
        offset -= 1;
    }
    offset
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

    #[test]
    fn semantic_tokens_share_editor_type_function_property_classification() {
        let source = "struct point { x: int } with:\n  our p.norm2 = p.x\n";
        let tokens = decode_tokens(semantic_tokens_for_source(source));
        let ty = token_type_index("type");
        let function = token_type_index("function");
        let property = token_type_index("property");

        assert!(
            tokens.contains(&(0, 7, 5, ty)),
            "expected struct name 'point' to be semantic type; got: {tokens:?}"
        );
        assert!(
            tokens.contains(&(1, 8, 5, function)),
            "expected dot-field 'norm2' to be semantic function; got: {tokens:?}"
        );
        assert!(
            !tokens.contains(&(1, 8, 5, property)),
            "expected dot-field 'norm2' not to be semantic property; got: {tokens:?}"
        );
    }

    #[test]
    fn diagnostics_use_decl_range_after_implicit_prelude() {
        let root = temp_root("diagnostic-range");
        std::fs::create_dir_all(root.join("lib").join("std")).unwrap();
        std::fs::write(root.join("lib").join("std.yu"), "mod prelude;\n").unwrap();
        std::fs::write(root.join("lib").join("std").join("prelude.yu"), "").unwrap();

        let source = "my x: bool = 1\n";
        let diagnostics = diagnostics_for_source(
            &root.join("main.yu"),
            source.to_string(),
            &crate::StdSourceOptions {
                std_root: Some(root.join("lib")),
            },
        );

        assert_eq!(diagnostics.len(), 1, "{diagnostics:?}");
        assert_eq!(
            diagnostics[0].range,
            Range {
                start: Position {
                    line: 0,
                    character: 3
                },
                end: Position {
                    line: 0,
                    character: 4
                },
            }
        );
        assert!(
            diagnostics[0].message.contains("type mismatch"),
            "{diagnostics:?}"
        );
    }

    #[test]
    fn diagnostics_use_unresolved_name_range() {
        let root = temp_root("unresolved-name-range");
        std::fs::create_dir_all(root.join("lib").join("std")).unwrap();
        std::fs::write(root.join("lib").join("std.yu"), "mod prelude;\n").unwrap();
        std::fs::write(root.join("lib").join("std").join("prelude.yu"), "").unwrap();

        let source = "my result = missing\n";
        let diagnostics = diagnostics_for_source(
            &root.join("main.yu"),
            source.to_string(),
            &crate::StdSourceOptions {
                std_root: Some(root.join("lib")),
            },
        );

        assert_eq!(diagnostics.len(), 1, "{diagnostics:?}");
        assert_eq!(
            diagnostics[0].range,
            Range {
                start: Position {
                    line: 0,
                    character: 12
                },
                end: Position {
                    line: 0,
                    character: 19
                },
            }
        );
        assert!(
            diagnostics[0].message.contains("unresolved value name"),
            "{diagnostics:?}"
        );
    }

    #[test]
    fn lsp_range_uses_utf16_columns() {
        let source = "my x = \"💡\"\nmy y: bool = 1\n";
        let start = source.find("y:").unwrap();
        let range = source_range_to_lsp_range(
            source,
            SourceRange {
                start,
                end: start + 1,
            },
        );

        assert_eq!(
            range,
            Range {
                start: Position {
                    line: 1,
                    character: 3
                },
                end: Position {
                    line: 1,
                    character: 4
                },
            }
        );
    }

    fn temp_root(name: &str) -> PathBuf {
        let root = std::env::temp_dir().join(format!(
            "yulang-server-{name}-{}",
            std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .unwrap()
                .as_nanos()
        ));
        let _ = std::fs::remove_dir_all(&root);
        root
    }

    fn token_type_index(name: &str) -> u32 {
        semantic_tokens::TOKEN_TYPES
            .iter()
            .position(|token| *token == name)
            .expect("semantic token type") as u32
    }

    fn decode_tokens(tokens: Vec<SemanticToken>) -> Vec<(u32, u32, u32, u32)> {
        let mut line = 0;
        let mut col = 0;
        tokens
            .into_iter()
            .map(|token| {
                line += token.delta_line;
                if token.delta_line == 0 {
                    col += token.delta_start;
                } else {
                    col = token.delta_start;
                }
                (line, col, token.length, token.token_type)
            })
            .collect()
    }
}
