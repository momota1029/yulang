use std::collections::HashMap;
use std::path::PathBuf;
use std::sync::Mutex;

use tower_lsp::jsonrpc::Result;
use tower_lsp::lsp_types::*;
use tower_lsp::{Client, LanguageServer, LspService, Server};
use yulang_editor::semantic_tokens;
use yulang_infer::{
    DefId, LowerState, Path as InferPath, collect_surface_diagnostics,
    lower_virtual_source_with_options, surface_diagnostic::SurfaceDiagnostic,
};
use yulang_source::{SourceOptions, collect_virtual_source_files_with_options};

struct Backend {
    client: Client,
    std_root: Option<PathBuf>,
    documents: Mutex<HashMap<Url, String>>,
}

impl Backend {
    fn source_options(&self, base_dir: Option<&std::path::Path>) -> SourceOptions {
        SourceOptions {
            std_root: self.resolved_std_root(base_dir),
            implicit_prelude: true,
            search_paths: vec![],
        }
    }

    async fn analyze(&self, uri: &Url) {
        let path = match uri.to_file_path() {
            Ok(p) => p,
            Err(_) => return,
        };
        let base_dir = path.parent().map(|parent| parent.to_path_buf());
        let source = self
            .documents
            .lock()
            .unwrap()
            .get(uri)
            .cloned()
            .or_else(|| std::fs::read_to_string(&path).ok());

        let Some(source) = source else {
            return;
        };

        let options = self.source_options(base_dir.as_deref());
        let diagnostics = tokio::task::spawn_blocking(move || {
            match lower_virtual_source_with_options(&source, base_dir, options) {
                Ok(lowered) => {
                    let surface = collect_surface_diagnostics(&lowered.state);
                    surface_to_lsp(&lowered.diagnostic_source, &source, surface)
                }
                Err(e) => vec![Diagnostic {
                    range: Range::default(),
                    severity: Some(DiagnosticSeverity::ERROR),
                    message: format!("failed to load source: {e}"),
                    ..Default::default()
                }],
            }
        })
        .await
        .unwrap_or_default();

        self.client
            .publish_diagnostics(uri.clone(), diagnostics, None)
            .await;
    }

    fn resolved_std_root(&self, base_dir: Option<&std::path::Path>) -> Option<PathBuf> {
        self.std_root
            .as_deref()
            .filter(|path| path.join("prelude.yu").is_file())
            .map(PathBuf::from)
            .or_else(|| base_dir.and_then(find_std_root_near))
    }
}

fn surface_to_lsp(
    diagnostic_source: &str,
    document_source: &str,
    diags: Vec<SurfaceDiagnostic>,
) -> Vec<Diagnostic> {
    let prefix_len = diagnostic_prefix_len(diagnostic_source, document_source);
    let line_starts = line_starts(document_source);
    diags
        .into_iter()
        .map(|d| {
            let range = d
                .span
                .and_then(|span| shift_span_to_document(span, prefix_len))
                .map(|span| byte_range_to_lsp(&line_starts, span))
                .unwrap_or_default();
            Diagnostic {
                range,
                severity: Some(DiagnosticSeverity::ERROR),
                message: d.message,
                ..Default::default()
            }
        })
        .collect()
}

fn diagnostic_prefix_len(diagnostic_source: &str, document_source: &str) -> usize {
    diagnostic_source
        .strip_suffix(document_source)
        .map(str::len)
        .unwrap_or(0)
}

fn shift_span_to_document(span: rowan::TextRange, prefix_len: usize) -> Option<rowan::TextRange> {
    let start = usize::from(span.start()).checked_sub(prefix_len)?;
    let end = usize::from(span.end()).checked_sub(prefix_len)?;
    Some(rowan::TextRange::new(
        (start as u32).into(),
        (end as u32).into(),
    ))
}

fn find_std_root_near(base_dir: &std::path::Path) -> Option<PathBuf> {
    for ancestor in base_dir.ancestors() {
        let candidate = ancestor.join("lib/std");
        if candidate.join("prelude.yu").is_file() {
            return Some(candidate);
        }
    }
    None
}

fn line_starts(text: &str) -> Vec<usize> {
    let mut starts = vec![0];
    for (i, c) in text.char_indices() {
        if c == '\n' {
            starts.push(i + 1);
        }
    }
    starts
}

fn byte_to_position(line_starts: &[usize], offset: usize) -> Position {
    let line = line_starts
        .partition_point(|&s| s <= offset)
        .saturating_sub(1);
    let line_start = line_starts[line];
    Position {
        line: line as u32,
        character: (offset - line_start) as u32,
    }
}

fn byte_range_to_lsp(line_starts: &[usize], span: rowan::TextRange) -> Range {
    Range {
        start: byte_to_position(line_starts, usize::from(span.start())),
        end: byte_to_position(line_starts, usize::from(span.end())),
    }
}

fn resolved_highlights_from_lower_state(
    state: &LowerState,
) -> semantic_tokens::ResolvedHighlightInfo {
    let mut info = semantic_tokens::ResolvedHighlightInfo::new();
    let canonical_paths = state.ctx.canonical_value_paths();

    for &def in state.enum_variant_tags.keys() {
        insert_constructor_def_highlight(state, &canonical_paths, def, &mut info);
    }
    for &def in state.enum_variant_patterns.keys() {
        insert_constructor_def_highlight(state, &canonical_paths, def, &mut info);
    }
    for &def in state.effect_op_args.keys() {
        insert_constructor_def_highlight(state, &canonical_paths, def, &mut info);
    }
    for (path, &def) in &state.same_path_effect_ops {
        insert_constructor_path_highlight(path, &mut info);
        insert_constructor_def_highlight(state, &canonical_paths, def, &mut info);
    }

    info
}

fn insert_constructor_def_highlight(
    state: &LowerState,
    canonical_paths: &std::collections::HashMap<DefId, InferPath>,
    def: DefId,
    info: &mut semantic_tokens::ResolvedHighlightInfo,
) {
    if let Some(name) = state.def_name(def) {
        info.insert_constructor_name(name.0.clone());
    }
    if let Some(path) = canonical_paths.get(&def) {
        insert_constructor_path_highlight(path, info);
    }
}

fn insert_constructor_path_highlight(
    path: &InferPath,
    info: &mut semantic_tokens::ResolvedHighlightInfo,
) {
    let mut segments = path
        .segments
        .iter()
        .map(|name| name.0.clone())
        .collect::<Vec<_>>();
    if let Some(last) = segments.last_mut() {
        if let Some(surface) = last.strip_suffix("#effect") {
            *last = surface.to_string();
        }
    }
    info.insert_constructor_path(segments);
}

#[tower_lsp::async_trait]
impl LanguageServer for Backend {
    async fn initialize(&self, _params: InitializeParams) -> Result<InitializeResult> {
        let legend = SemanticTokensLegend {
            token_types: semantic_tokens::TOKEN_TYPES
                .iter()
                .map(|s| SemanticTokenType::new(s))
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
                name: "yulang-lsp".to_string(),
                version: Some(env!("CARGO_PKG_VERSION").to_string()),
            }),
        })
    }

    async fn initialized(&self, _: InitializedParams) {
        self.client
            .log_message(MessageType::INFO, "yulang-lsp initialized")
            .await;
    }

    async fn shutdown(&self) -> Result<()> {
        Ok(())
    }

    async fn did_open(&self, params: DidOpenTextDocumentParams) {
        self.documents
            .lock()
            .unwrap()
            .insert(params.text_document.uri.clone(), params.text_document.text);
        self.analyze(&params.text_document.uri).await;
    }

    async fn did_change(&self, params: DidChangeTextDocumentParams) {
        if let Some(change) = params.content_changes.into_iter().last() {
            self.documents
                .lock()
                .unwrap()
                .insert(params.text_document.uri.clone(), change.text);
        }
        self.analyze(&params.text_document.uri).await;
    }

    async fn did_save(&self, params: DidSaveTextDocumentParams) {
        if let Some(text) = params.text {
            self.documents
                .lock()
                .unwrap()
                .insert(params.text_document.uri.clone(), text);
        }
        self.analyze(&params.text_document.uri).await;
    }

    async fn did_close(&self, params: DidCloseTextDocumentParams) {
        self.documents
            .lock()
            .unwrap()
            .remove(&params.text_document.uri);
        self.client
            .publish_diagnostics(params.text_document.uri, Vec::new(), None)
            .await;
    }

    async fn semantic_tokens_full(
        &self,
        params: SemanticTokensParams,
    ) -> Result<Option<SemanticTokensResult>> {
        let uri = params.text_document.uri;
        let source = self.documents.lock().unwrap().get(&uri).cloned();

        let base_dir = uri.to_file_path().ok().and_then(|path| {
            if path.is_dir() {
                Some(path)
            } else {
                path.parent().map(|parent| parent.to_path_buf())
            }
        });
        let options = self.source_options(base_dir.as_deref());

        let data = tokio::task::spawn_blocking(move || match source {
            Some(source) => {
                let op_options = options.clone();
                let lower_options = options;
                let lower_base_dir = base_dir.clone();
                let op_table =
                    collect_virtual_source_files_with_options(&source, base_dir, op_options)
                        .ok()
                        .and_then(|source_set| {
                            source_set
                                .entry_files()
                                .next()
                                .map(|file| file.op_table.clone())
                        });
                let highlights =
                    lower_virtual_source_with_options(&source, lower_base_dir, lower_options)
                        .ok()
                        .map(|lowered| resolved_highlights_from_lower_state(&lowered.state));
                semantic_tokens::compute_with_op_table_and_highlights(
                    &source,
                    op_table,
                    highlights.as_ref(),
                )
            }
            None => uri
                .to_file_path()
                .ok()
                .and_then(|path| std::fs::read_to_string(path).ok())
                .map(|source| semantic_tokens::compute(&source))
                .unwrap_or_default(),
        })
        .await
        .unwrap_or_default();

        Ok(Some(SemanticTokensResult::Tokens(SemanticTokens {
            result_id: None,
            data: data
                .chunks(5)
                .map(|c| SemanticToken {
                    delta_line: c[0],
                    delta_start: c[1],
                    length: c[2],
                    token_type: c[3],
                    token_modifiers_bitset: c[4],
                })
                .collect(),
        })))
    }
}

#[tokio::main]
async fn main() {
    let std_root = std::env::var("YULANG_STD")
        .ok()
        .map(PathBuf::from)
        .or_else(|| {
            std::env::current_exe()
                .ok()
                .and_then(|p| p.parent()?.parent()?.parent().map(|p| p.join("lib/std")))
        });

    let stdin = tokio::io::stdin();
    let stdout = tokio::io::stdout();

    let (service, socket) = LspService::new(|client| Backend {
        client,
        std_root,
        documents: Mutex::new(HashMap::new()),
    });
    Server::new(stdin, stdout, socket).serve(service).await;
}
