use std::collections::HashMap;
use std::path::{Path, PathBuf};
use std::sync::{Arc, Mutex};
use std::time::Duration;

use tokio::sync::Semaphore;
use tower_lsp::lsp_types::*;
use tower_lsp::{Client, LanguageServer, LspService, Server};
use yulang_editor::semantic_tokens;

use crate::source::SourceTextAnalysis;
use crate::{SourceDefinition, SourceHover, SourceLocation, SourceRange, SourceRename};

const LSP_ANALYSIS_TIMEOUT: Duration = Duration::from_secs(3);
const LSP_ANALYSIS_DEBOUNCE: Duration = Duration::from_millis(150);
const LSP_REQUEST_TIMEOUT: Duration = Duration::from_secs(5);

struct Backend {
    client: Client,
    std_root: Option<PathBuf>,
    documents: Arc<Mutex<HashMap<Url, String>>>,
    analysis_versions: Arc<Mutex<HashMap<Url, u64>>>,
    request_cache: Arc<Mutex<HashMap<LspRequestCacheKey, LspRequestCacheValue>>>,
    analysis_slots: Arc<Semaphore>,
    request_slots: Arc<Semaphore>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
struct LspRequestCacheKey {
    uri: Url,
    version: u64,
    kind: LspRequestKind,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
enum LspRequestKind {
    Hover {
        position: PositionKey,
    },
    Definition {
        position: PositionKey,
    },
    References {
        position: PositionKey,
        include_declaration: bool,
    },
    PrepareRename {
        position: PositionKey,
    },
    Rename {
        position: PositionKey,
        new_name: String,
    },
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
struct PositionKey {
    line: u32,
    character: u32,
}

impl From<Position> for PositionKey {
    fn from(position: Position) -> Self {
        Self {
            line: position.line,
            character: position.character,
        }
    }
}

#[derive(Debug, Clone)]
enum LspRequestCacheValue {
    Hover(Option<Hover>),
    Definition(Option<Location>),
    References(Vec<Location>),
    PrepareRename(Option<PrepareRenameResponse>),
    Rename(Option<WorkspaceEdit>),
}

impl Backend {
    fn schedule_analysis(&self, uri: Url) {
        let version = self.bump_analysis_version(&uri);
        self.clear_request_cache(&uri);
        let path = match uri.to_file_path() {
            Ok(path) => path,
            Err(_) => return,
        };
        let options = crate::StdSourceOptions {
            std_root: self.std_root.clone(),
        };
        let client = self.client.clone();
        let documents = Arc::clone(&self.documents);
        let versions = Arc::clone(&self.analysis_versions);
        let slots = Arc::clone(&self.analysis_slots);
        tokio::spawn(async move {
            tokio::time::sleep(LSP_ANALYSIS_DEBOUNCE).await;
            if !is_current_analysis_version(&versions, &uri, version) {
                return;
            }
            let source = documents
                .lock()
                .unwrap()
                .get(&uri)
                .cloned()
                .or_else(|| std::fs::read_to_string(&path).ok());
            let Some(source) = source else {
                return;
            };
            let result = run_diagnostics_with_timeout(slots, path, source, options).await;
            if !is_current_analysis_version(&versions, &uri, version) {
                return;
            }
            match result {
                DiagnosticsRunResult::Completed(diagnostics) => {
                    client.publish_diagnostics(uri, diagnostics, None).await;
                }
                DiagnosticsRunResult::Busy => {}
                DiagnosticsRunResult::TimedOut => {
                    client
                        .log_message(
                            MessageType::WARNING,
                            "Yulang diagnostics timed out; editor features remain available",
                        )
                        .await;
                }
                DiagnosticsRunResult::WorkerFailed(error) => {
                    client
                        .log_message(
                            MessageType::ERROR,
                            format!("Yulang diagnostics worker failed: {error}"),
                        )
                        .await;
                }
            }
        });
    }

    fn bump_analysis_version(&self, uri: &Url) -> u64 {
        let mut versions = self.analysis_versions.lock().unwrap();
        let next = versions.get(uri).copied().unwrap_or(0).wrapping_add(1);
        versions.insert(uri.clone(), next);
        next
    }

    fn cancel_analysis(&self, uri: &Url) {
        self.bump_analysis_version(uri);
        self.clear_request_cache(uri);
    }

    fn current_analysis_version(&self, uri: &Url) -> u64 {
        self.analysis_versions
            .lock()
            .unwrap()
            .get(uri)
            .copied()
            .unwrap_or(0)
    }

    fn cached_request(&self, key: &LspRequestCacheKey) -> Option<LspRequestCacheValue> {
        self.request_cache.lock().unwrap().get(key).cloned()
    }

    fn store_request(&self, key: LspRequestCacheKey, value: LspRequestCacheValue) {
        self.request_cache.lock().unwrap().insert(key, value);
    }

    fn clear_request_cache(&self, uri: &Url) {
        self.request_cache
            .lock()
            .unwrap()
            .retain(|key, _| &key.uri != uri);
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

async fn run_diagnostics_with_timeout(
    slots: Arc<Semaphore>,
    path: PathBuf,
    source: String,
    options: crate::StdSourceOptions,
) -> DiagnosticsRunResult {
    let Ok(permit) = slots.try_acquire_owned() else {
        return DiagnosticsRunResult::Busy;
    };
    let handle = tokio::task::spawn_blocking(move || {
        let _permit = permit;
        diagnostics_for_source(&path, source, &options)
    });
    match tokio::time::timeout(LSP_ANALYSIS_TIMEOUT, handle).await {
        Ok(Ok(diagnostics)) => DiagnosticsRunResult::Completed(diagnostics),
        Ok(Err(error)) => DiagnosticsRunResult::WorkerFailed(error.to_string()),
        Err(_) => DiagnosticsRunResult::TimedOut,
    }
}

#[derive(Debug)]
enum DiagnosticsRunResult {
    Completed(Vec<Diagnostic>),
    Busy,
    TimedOut,
    WorkerFailed(String),
}

fn is_current_analysis_version(
    versions: &Arc<Mutex<HashMap<Url, u64>>>,
    uri: &Url,
    version: u64,
) -> bool {
    versions.lock().unwrap().get(uri).copied().unwrap_or(0) == version
}

fn source_analysis_for_source(
    path: &Path,
    source: String,
    options: &crate::StdSourceOptions,
) -> Result<SourceTextAnalysis, crate::RouteError> {
    crate::source::source_text_analysis_with_std_options(path, source.clone(), options)
        .or_else(|_| crate::source::source_text_analysis(path, source))
}

fn diagnostics_for_analysis(
    path: &Path,
    source: &str,
    analysis: &SourceTextAnalysis,
) -> Vec<Diagnostic> {
    let uri = Url::from_file_path(path).ok();
    analysis
        .analyze()
        .diagnostics
        .into_iter()
        .map(|diagnostic| {
            let mut message = match diagnostic.label {
                Some(label) => format!("{label}: {}", diagnostic.message),
                None => diagnostic.message,
            };
            if let Some(hint) = diagnostic.hint {
                message.push_str("\nhint: ");
                message.push_str(&hint);
            }
            let related_information = uri.as_ref().and_then(|uri| {
                let related = diagnostic
                    .related
                    .into_iter()
                    .map(|related| DiagnosticRelatedInformation {
                        location: Location {
                            uri: uri.clone(),
                            range: lsp_range_for_root_source(
                                source,
                                related.range,
                                analysis.root_has_implicit_prelude(),
                            ),
                        },
                        message: related.message,
                    })
                    .collect::<Vec<_>>();
                (!related.is_empty()).then_some(related)
            });
            Diagnostic {
                range: diagnostic
                    .range
                    .map(|range| {
                        lsp_range_for_root_source(
                            source,
                            range,
                            analysis.root_has_implicit_prelude(),
                        )
                    })
                    .unwrap_or_default(),
                severity: Some(DiagnosticSeverity::ERROR),
                code: diagnostic.code.map(NumberOrString::String),
                source: Some("yulang".to_string()),
                message,
                related_information,
                ..Default::default()
            }
        })
        .collect()
}

fn diagnostic_for_route_error(error: crate::RouteError) -> Diagnostic {
    Diagnostic {
        range: Range::default(),
        severity: Some(DiagnosticSeverity::ERROR),
        source: Some("yulang".to_string()),
        message: error.to_string(),
        ..Default::default()
    }
}

fn diagnostics_for_source(
    path: &Path,
    source: String,
    options: &crate::StdSourceOptions,
) -> Vec<Diagnostic> {
    match crate::source::source_text_analysis_with_std_options(path, source.clone(), options) {
        Ok(analysis) => diagnostics_for_analysis(path, &source, &analysis),
        Err(error) => vec![diagnostic_for_route_error(error)],
    }
}

fn hover_for_source(
    path: &Path,
    source: String,
    position: Position,
    options: &crate::StdSourceOptions,
) -> Option<Hover> {
    let analysis = source_analysis_for_source(path, source.clone(), options).ok()?;
    hover_for_analysis(&source, &analysis, position)
}

fn definition_for_source(
    path: &Path,
    source: String,
    position: Position,
    options: &crate::StdSourceOptions,
) -> Option<Location> {
    let analysis = source_analysis_for_source(path, source.clone(), options).ok()?;
    definition_for_analysis(path, &source, &analysis, position)
}

fn references_for_source(
    path: &Path,
    source: String,
    position: Position,
    include_declaration: bool,
    options: &crate::StdSourceOptions,
) -> Vec<Location> {
    let Ok(analysis) = source_analysis_for_source(path, source.clone(), options) else {
        return Vec::new();
    };
    references_for_analysis(path, &source, &analysis, position, include_declaration)
}

fn prepare_rename_for_source(
    path: &Path,
    source: String,
    position: Position,
    options: &crate::StdSourceOptions,
) -> Option<PrepareRenameResponse> {
    let analysis = source_analysis_for_source(path, source.clone(), options).ok()?;
    prepare_rename_for_analysis(&source, &analysis, position)
}

fn rename_for_source(
    path: &Path,
    source: String,
    position: Position,
    new_name: &str,
    options: &crate::StdSourceOptions,
) -> Option<WorkspaceEdit> {
    let analysis = source_analysis_for_source(path, source.clone(), options).ok()?;
    rename_for_analysis(path, &source, &analysis, position, new_name)
}

fn hover_for_analysis(
    source: &str,
    analysis: &SourceTextAnalysis,
    position: Position,
) -> Option<Hover> {
    let byte_offset = position_to_byte_offset(&source, position)?;
    let hover = analysis.hover(byte_offset)?;
    Some(lsp_hover_for_source_hover(
        &source,
        hover,
        analysis.root_has_implicit_prelude(),
    ))
}

fn definition_for_analysis(
    path: &Path,
    source: &str,
    analysis: &SourceTextAnalysis,
    position: Position,
) -> Option<Location> {
    let byte_offset = position_to_byte_offset(&source, position)?;
    let definition = analysis.definition(byte_offset)?;
    lsp_location_for_source_definition(
        path,
        source,
        definition,
        analysis.root_has_implicit_prelude(),
    )
}

fn references_for_analysis(
    path: &Path,
    source: &str,
    analysis: &SourceTextAnalysis,
    position: Position,
    include_declaration: bool,
) -> Vec<Location> {
    let Some(byte_offset) = position_to_byte_offset(&source, position) else {
        return Vec::new();
    };
    let locations = analysis.references(byte_offset, include_declaration);
    locations
        .into_iter()
        .filter_map(|location| {
            lsp_location_for_source_location(
                path,
                source,
                location,
                analysis.root_has_implicit_prelude(),
            )
        })
        .collect()
}

fn prepare_rename_for_analysis(
    source: &str,
    analysis: &SourceTextAnalysis,
    position: Position,
) -> Option<PrepareRenameResponse> {
    let byte_offset = position_to_byte_offset(&source, position)?;
    let range = analysis.prepare_rename(byte_offset)?;
    Some(PrepareRenameResponse::Range(lsp_range_for_root_source(
        &source,
        range,
        analysis.root_has_implicit_prelude(),
    )))
}

fn rename_for_analysis(
    path: &Path,
    source: &str,
    analysis: &SourceTextAnalysis,
    position: Position,
    new_name: &str,
) -> Option<WorkspaceEdit> {
    let byte_offset = position_to_byte_offset(&source, position)?;
    let rename = analysis.rename(byte_offset, new_name)?;
    workspace_edit_for_source_rename(path, source, rename, analysis.root_has_implicit_prelude())
}

fn lsp_hover_for_source_hover(
    source: &str,
    hover: SourceHover,
    root_has_implicit_prelude: bool,
) -> Hover {
    Hover {
        contents: HoverContents::Markup(MarkupContent {
            kind: MarkupKind::Markdown,
            value: format!("```yulang\n{}\n```", hover.contents),
        }),
        range: Some(lsp_range_for_root_source(
            source,
            hover.range,
            root_has_implicit_prelude,
        )),
    }
}

fn lsp_location_for_source_definition(
    root_path: &Path,
    root_source: &str,
    definition: SourceDefinition,
    root_has_implicit_prelude: bool,
) -> Option<Location> {
    lsp_location_for_source_location(
        root_path,
        root_source,
        definition.target,
        root_has_implicit_prelude,
    )
}

fn lsp_location_for_source_location(
    root_path: &Path,
    root_source: &str,
    location: SourceLocation,
    root_has_implicit_prelude: bool,
) -> Option<Location> {
    let uri = Url::from_file_path(&location.path).ok()?;
    let range = if location.path == root_path {
        lsp_range_for_root_source(root_source, location.range, root_has_implicit_prelude)
    } else {
        let source = std::fs::read_to_string(&location.path).ok()?;
        source_range_to_lsp_range(&source, location.range)
    };
    Some(Location { uri, range })
}

fn workspace_edit_for_source_rename(
    root_path: &Path,
    root_source: &str,
    rename: SourceRename,
    root_has_implicit_prelude: bool,
) -> Option<WorkspaceEdit> {
    let mut changes: HashMap<Url, Vec<TextEdit>> = HashMap::new();
    for edit in rename.edits {
        let location = lsp_location_for_source_location(
            root_path,
            root_source,
            edit.location,
            root_has_implicit_prelude,
        )?;
        changes.entry(location.uri).or_default().push(TextEdit {
            range: location.range,
            new_text: edit.new_text,
        });
    }
    (!changes.is_empty()).then_some(WorkspaceEdit {
        changes: Some(changes),
        document_changes: None,
        change_annotations: None,
    })
}

fn lsp_range_for_root_source(
    source: &str,
    range: SourceRange,
    root_has_implicit_prelude: bool,
) -> Range {
    if root_has_implicit_prelude {
        lsp_range_for_loaded_root_range(source, range)
    } else {
        source_range_to_lsp_range(source, range)
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

fn position_to_byte_offset(source: &str, position: Position) -> Option<usize> {
    let line_starts = compute_line_starts(source);
    let line_start = *line_starts.get(position.line as usize)?;
    let line_end = line_starts
        .get(position.line as usize + 1)
        .map(|next| next.saturating_sub(1))
        .unwrap_or(source.len());
    let mut utf16_column = 0u32;
    for (relative, ch) in source[line_start..line_end].char_indices() {
        if utf16_column == position.character {
            return Some(line_start + relative);
        }
        let next_column = utf16_column + ch.len_utf16() as u32;
        if position.character < next_column {
            return None;
        }
        utf16_column = next_column;
    }
    (utf16_column == position.character).then_some(line_end)
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
                hover_provider: Some(HoverProviderCapability::Simple(true)),
                definition_provider: Some(OneOf::Left(true)),
                references_provider: Some(OneOf::Left(true)),
                rename_provider: Some(OneOf::Right(RenameOptions {
                    prepare_provider: Some(true),
                    work_done_progress_options: Default::default(),
                })),
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
        self.schedule_analysis(params.text_document.uri);
    }

    async fn did_change(&self, params: DidChangeTextDocumentParams) {
        if let Some(change) = params.content_changes.into_iter().last() {
            self.documents
                .lock()
                .unwrap()
                .insert(params.text_document.uri.clone(), change.text);
        }
        self.schedule_analysis(params.text_document.uri);
    }

    async fn did_save(&self, params: DidSaveTextDocumentParams) {
        if let Some(text) = params.text {
            self.documents
                .lock()
                .unwrap()
                .insert(params.text_document.uri.clone(), text);
        }
        self.schedule_analysis(params.text_document.uri);
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

    async fn hover(&self, params: HoverParams) -> tower_lsp::jsonrpc::Result<Option<Hover>> {
        let uri = params.text_document_position_params.text_document.uri;
        let position = params.text_document_position_params.position;
        let path = match uri.to_file_path() {
            Ok(path) => path,
            Err(_) => return Ok(None),
        };
        let Some(source) = self.document_source(&uri) else {
            return Ok(None);
        };
        let options = crate::StdSourceOptions {
            std_root: self.std_root.clone(),
        };
        let key = LspRequestCacheKey {
            uri: uri.clone(),
            version: self.current_analysis_version(&uri),
            kind: LspRequestKind::Hover {
                position: position.into(),
            },
        };
        if let Some(LspRequestCacheValue::Hover(hover)) = self.cached_request(&key) {
            return Ok(hover);
        }
        let Ok(permit) = self.request_slots.clone().try_acquire_owned() else {
            return Ok(None);
        };
        let handle = tokio::task::spawn_blocking(move || {
            let _permit = permit;
            hover_for_source(&path, source, position, &options)
        });
        let hover = match tokio::time::timeout(LSP_REQUEST_TIMEOUT, handle).await {
            Ok(Ok(hover)) => hover,
            Ok(Err(_)) | Err(_) => None,
        };
        if self.current_analysis_version(&uri) == key.version {
            self.store_request(key, LspRequestCacheValue::Hover(hover.clone()));
        }
        Ok(hover)
    }

    async fn goto_definition(
        &self,
        params: GotoDefinitionParams,
    ) -> tower_lsp::jsonrpc::Result<Option<GotoDefinitionResponse>> {
        let uri = params.text_document_position_params.text_document.uri;
        let position = params.text_document_position_params.position;
        let path = match uri.to_file_path() {
            Ok(path) => path,
            Err(_) => return Ok(None),
        };
        let Some(source) = self.document_source(&uri) else {
            return Ok(None);
        };
        let options = crate::StdSourceOptions {
            std_root: self.std_root.clone(),
        };
        let key = LspRequestCacheKey {
            uri: uri.clone(),
            version: self.current_analysis_version(&uri),
            kind: LspRequestKind::Definition {
                position: position.into(),
            },
        };
        if let Some(LspRequestCacheValue::Definition(location)) = self.cached_request(&key) {
            return Ok(location.map(GotoDefinitionResponse::Scalar));
        }
        let Ok(permit) = self.request_slots.clone().try_acquire_owned() else {
            return Ok(None);
        };
        let handle = tokio::task::spawn_blocking(move || {
            let _permit = permit;
            definition_for_source(&path, source, position, &options)
        });
        let location = match tokio::time::timeout(LSP_REQUEST_TIMEOUT, handle).await {
            Ok(Ok(location)) => location,
            Ok(Err(_)) | Err(_) => None,
        };
        if self.current_analysis_version(&uri) == key.version {
            self.store_request(key, LspRequestCacheValue::Definition(location.clone()));
        }
        Ok(location.map(GotoDefinitionResponse::Scalar))
    }

    async fn references(
        &self,
        params: ReferenceParams,
    ) -> tower_lsp::jsonrpc::Result<Option<Vec<Location>>> {
        let uri = params.text_document_position.text_document.uri;
        let position = params.text_document_position.position;
        let include_declaration = params.context.include_declaration;
        let path = match uri.to_file_path() {
            Ok(path) => path,
            Err(_) => return Ok(None),
        };
        let Some(source) = self.document_source(&uri) else {
            return Ok(None);
        };
        let options = crate::StdSourceOptions {
            std_root: self.std_root.clone(),
        };
        let key = LspRequestCacheKey {
            uri: uri.clone(),
            version: self.current_analysis_version(&uri),
            kind: LspRequestKind::References {
                position: position.into(),
                include_declaration,
            },
        };
        if let Some(LspRequestCacheValue::References(locations)) = self.cached_request(&key) {
            return Ok(Some(locations));
        }
        let Ok(permit) = self.request_slots.clone().try_acquire_owned() else {
            return Ok(None);
        };
        let handle = tokio::task::spawn_blocking(move || {
            let _permit = permit;
            references_for_source(&path, source, position, include_declaration, &options)
        });
        let locations = match tokio::time::timeout(LSP_REQUEST_TIMEOUT, handle).await {
            Ok(Ok(locations)) => locations,
            Ok(Err(_)) | Err(_) => Vec::new(),
        };
        if self.current_analysis_version(&uri) == key.version {
            self.store_request(key, LspRequestCacheValue::References(locations.clone()));
        }
        Ok(Some(locations))
    }

    async fn prepare_rename(
        &self,
        params: TextDocumentPositionParams,
    ) -> tower_lsp::jsonrpc::Result<Option<PrepareRenameResponse>> {
        let uri = params.text_document.uri;
        let position = params.position;
        let path = match uri.to_file_path() {
            Ok(path) => path,
            Err(_) => return Ok(None),
        };
        let Some(source) = self.document_source(&uri) else {
            return Ok(None);
        };
        let options = crate::StdSourceOptions {
            std_root: self.std_root.clone(),
        };
        let key = LspRequestCacheKey {
            uri: uri.clone(),
            version: self.current_analysis_version(&uri),
            kind: LspRequestKind::PrepareRename {
                position: position.into(),
            },
        };
        if let Some(LspRequestCacheValue::PrepareRename(response)) = self.cached_request(&key) {
            return Ok(response);
        }
        let Ok(permit) = self.request_slots.clone().try_acquire_owned() else {
            return Ok(None);
        };
        let handle = tokio::task::spawn_blocking(move || {
            let _permit = permit;
            prepare_rename_for_source(&path, source, position, &options)
        });
        let response = match tokio::time::timeout(LSP_REQUEST_TIMEOUT, handle).await {
            Ok(Ok(response)) => response,
            Ok(Err(_)) | Err(_) => None,
        };
        if self.current_analysis_version(&uri) == key.version {
            self.store_request(key, LspRequestCacheValue::PrepareRename(response.clone()));
        }
        Ok(response)
    }

    async fn rename(
        &self,
        params: RenameParams,
    ) -> tower_lsp::jsonrpc::Result<Option<WorkspaceEdit>> {
        let uri = params.text_document_position.text_document.uri;
        let position = params.text_document_position.position;
        let new_name = params.new_name;
        let path = match uri.to_file_path() {
            Ok(path) => path,
            Err(_) => return Ok(None),
        };
        let Some(source) = self.document_source(&uri) else {
            return Ok(None);
        };
        let options = crate::StdSourceOptions {
            std_root: self.std_root.clone(),
        };
        let key = LspRequestCacheKey {
            uri: uri.clone(),
            version: self.current_analysis_version(&uri),
            kind: LspRequestKind::Rename {
                position: position.into(),
                new_name: new_name.clone(),
            },
        };
        if let Some(LspRequestCacheValue::Rename(edit)) = self.cached_request(&key) {
            return Ok(edit);
        }
        let Ok(permit) = self.request_slots.clone().try_acquire_owned() else {
            return Ok(None);
        };
        let handle = tokio::task::spawn_blocking(move || {
            let _permit = permit;
            rename_for_source(&path, source, position, &new_name, &options)
        });
        let edit = match tokio::time::timeout(LSP_REQUEST_TIMEOUT, handle).await {
            Ok(Ok(edit)) => edit,
            Ok(Err(_)) | Err(_) => None,
        };
        if self.current_analysis_version(&uri) == key.version {
            self.store_request(key, LspRequestCacheValue::Rename(edit.clone()));
        }
        Ok(edit)
    }
}

pub async fn serve(std_root: Option<PathBuf>) {
    let stdin = tokio::io::stdin();
    let stdout = tokio::io::stdout();
    let (service, socket) = LspService::new(|client| Backend {
        client,
        std_root,
        documents: Arc::new(Mutex::new(HashMap::new())),
        analysis_versions: Arc::new(Mutex::new(HashMap::new())),
        request_cache: Arc::new(Mutex::new(HashMap::new())),
        analysis_slots: Arc::new(Semaphore::new(1)),
        request_slots: Arc::new(Semaphore::new(2)),
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

    fn assert_diagnostic_code(diagnostic: &Diagnostic, expected: &str) {
        assert_eq!(
            diagnostic.code.as_ref(),
            Some(&NumberOrString::String(expected.to_string())),
            "{diagnostic:?}"
        );
    }

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
        assert_diagnostic_code(&diagnostics[0], "yulang.type-mismatch");
        let related = diagnostics[0]
            .related_information
            .as_ref()
            .expect("type mismatch should carry related ranges");
        assert_eq!(related.len(), 2, "{related:?}");
        assert_eq!(
            related[0].message,
            "expected type comes from this type annotation: bool"
        );
        assert_eq!(
            related[0].location.range,
            Range {
                start: Position {
                    line: 0,
                    character: 6
                },
                end: Position {
                    line: 0,
                    character: 10
                },
            }
        );
        assert_eq!(
            related[1].message,
            "actual type comes from this expression: int"
        );
        assert_eq!(
            related[1].location.range,
            Range {
                start: Position {
                    line: 0,
                    character: 13
                },
                end: Position {
                    line: 0,
                    character: 14
                },
            }
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
        assert!(
            diagnostics[0]
                .message
                .contains("hint: define `missing` before this use"),
            "{diagnostics:?}"
        );
        assert_diagnostic_code(&diagnostics[0], "yulang.unresolved-value");
    }

    #[test]
    fn diagnostics_use_unresolved_type_name_range() {
        let root = temp_root("unresolved-type-name-range");
        std::fs::create_dir_all(root.join("lib").join("std")).unwrap();
        std::fs::write(root.join("lib").join("std.yu"), "mod prelude;\n").unwrap();
        std::fs::write(root.join("lib").join("std").join("prelude.yu"), "").unwrap();

        let source = "my x: missing_type = 1\n";
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
                    character: 6
                },
                end: Position {
                    line: 0,
                    character: 18
                },
            }
        );
        assert!(
            diagnostics[0].message.contains("unresolved type name"),
            "{diagnostics:?}"
        );
        assert!(
            diagnostics[0]
                .message
                .contains("hint: define type `missing_type` before this annotation"),
            "{diagnostics:?}"
        );
        assert_diagnostic_code(&diagnostics[0], "yulang.unresolved-type");
    }

    #[test]
    fn diagnostics_use_unsupported_type_syntax_range() {
        let root = temp_root("unsupported-type-syntax-range");
        std::fs::create_dir_all(root.join("lib").join("std")).unwrap();
        std::fs::write(root.join("lib").join("std.yu"), "mod prelude;\n").unwrap();
        std::fs::write(root.join("lib").join("std").join("prelude.yu"), "").unwrap();

        let source = "my x: { a: int, b: int } = { a: 1 }\n";
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
                    character: 6
                },
                end: Position {
                    line: 0,
                    character: 25
                },
            }
        );
        assert!(
            diagnostics[0]
                .message
                .contains("unsupported type annotation syntax"),
            "{diagnostics:?}"
        );
        assert_diagnostic_code(&diagnostics[0], "yulang.unsupported-type-syntax");
    }

    #[test]
    fn diagnostics_use_top_level_mutable_binding_range() {
        let root = temp_root("top-level-mutable-binding-range");
        std::fs::create_dir_all(root.join("lib").join("std")).unwrap();
        std::fs::write(root.join("lib").join("std.yu"), "mod prelude;\n").unwrap();
        std::fs::write(root.join("lib").join("std").join("prelude.yu"), "").unwrap();

        let source = "my $x = 0\n";
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
                    character: 5
                },
            }
        );
        assert!(
            diagnostics[0].message.contains("top-level mutable binding"),
            "{diagnostics:?}"
        );
        assert_diagnostic_code(&diagnostics[0], "yulang.top-level-mutable-binding");
    }

    #[test]
    fn diagnostics_use_rule_lazy_quantifier_range() {
        let root = temp_root("rule-lazy-quantifier-range");
        std::fs::create_dir_all(root.join("lib").join("std")).unwrap();
        std::fs::write(root.join("lib").join("std.yu"), "mod prelude;\n").unwrap();
        std::fs::write(root.join("lib").join("std").join("prelude.yu"), "").unwrap();

        let source = "my p = rule { \"ha\"*? }\n";
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
                    character: 18
                },
                end: Position {
                    line: 0,
                    character: 20
                },
            }
        );
        assert!(
            diagnostics[0]
                .message
                .contains("rule lazy quantifier `*?` is not supported"),
            "{diagnostics:?}"
        );
        assert_diagnostic_code(&diagnostics[0], "yulang.unsupported-rule-lazy-quantifier");
    }

    #[test]
    fn diagnostics_use_unclosed_paren_syntax_range() {
        let root = temp_root("unclosed-paren-syntax-range");
        std::fs::create_dir_all(root.join("lib").join("std")).unwrap();
        std::fs::write(root.join("lib").join("std.yu"), "mod prelude;\n").unwrap();
        std::fs::write(root.join("lib").join("std").join("prelude.yu"), "").unwrap();

        let source = "my x = (1\n";
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
                    character: 9
                },
                end: Position {
                    line: 0,
                    character: 9
                },
            }
        );
        assert!(
            diagnostics[0].message.contains("unexpected end of input"),
            "{diagnostics:?}"
        );
        assert_diagnostic_code(&diagnostics[0], "yulang.syntax");
    }

    #[test]
    fn diagnostics_use_trailing_operator_syntax_range() {
        let root = temp_root("trailing-operator-syntax-range");
        std::fs::create_dir_all(root.join("lib").join("std")).unwrap();
        std::fs::write(root.join("lib").join("std.yu"), "mod prelude;\n").unwrap();
        std::fs::write(root.join("lib").join("std").join("prelude.yu"), "").unwrap();

        let source = "my x = 1 +\n";
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
                    character: 9
                },
                end: Position {
                    line: 0,
                    character: 10
                },
            }
        );
        assert!(
            diagnostics[0].message.contains("unexpected token"),
            "{diagnostics:?}"
        );
        assert_diagnostic_code(&diagnostics[0], "yulang.syntax");
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

    #[test]
    fn position_to_byte_offset_rejects_split_utf16_surrogate() {
        let source = "💡x\n";

        assert_eq!(
            position_to_byte_offset(
                source,
                Position {
                    line: 0,
                    character: 2,
                },
            ),
            Some("💡".len())
        );
        assert_eq!(
            position_to_byte_offset(
                source,
                Position {
                    line: 0,
                    character: 1,
                },
            ),
            None
        );
    }

    #[test]
    fn hover_for_source_reports_type_at_reference() {
        let root = temp_root("hover-type-reference");
        std::fs::create_dir_all(root.join("lib").join("std")).unwrap();
        std::fs::write(root.join("lib").join("std.yu"), "mod prelude;\n").unwrap();
        std::fs::write(root.join("lib").join("std").join("prelude.yu"), "").unwrap();

        let source = "my x: int = 1\nmy y = x\n";
        let hover = hover_for_source(
            &root.join("main.yu"),
            source.to_string(),
            Position {
                line: 1,
                character: 7,
            },
            &crate::StdSourceOptions {
                std_root: Some(root.join("lib")),
            },
        )
        .unwrap();

        assert_eq!(
            hover.range,
            Some(Range {
                start: Position {
                    line: 1,
                    character: 7
                },
                end: Position {
                    line: 1,
                    character: 8
                },
            })
        );
        assert_eq!(
            hover.contents,
            HoverContents::Markup(MarkupContent {
                kind: MarkupKind::Markdown,
                value: "```yulang\nx: int\n```".to_string(),
            })
        );
    }

    #[test]
    fn definition_for_source_reports_reference_target_location() {
        let root = temp_root("definition-reference-target-location");
        std::fs::create_dir_all(root.join("lib").join("std")).unwrap();
        std::fs::write(root.join("lib").join("std.yu"), "mod prelude;\n").unwrap();
        std::fs::write(root.join("lib").join("std").join("prelude.yu"), "").unwrap();

        let entry = root.join("main.yu");
        let source = "my x: int = 1\nmy y = x\n";
        let location = definition_for_source(
            &entry,
            source.to_string(),
            Position {
                line: 1,
                character: 7,
            },
            &crate::StdSourceOptions {
                std_root: Some(root.join("lib")),
            },
        )
        .unwrap();

        assert_eq!(location.uri, Url::from_file_path(&entry).unwrap());
        assert_eq!(
            location.range,
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
    }

    #[test]
    fn definition_for_source_reports_std_file_method_target_location() {
        let std_root = workspace_std_root();
        let entry = std_root.join("std").join("core").join("ops.yu");
        let source = std::fs::read_to_string(&entry).unwrap();
        let offset = source.find("label.next").unwrap() + "label.".len();
        let position = byte_offset_to_position(&source, &compute_line_starts(&source), offset);
        let target = std_root.join("std").join("control").join("flow.yu");
        let target_source = std::fs::read_to_string(&target).unwrap();
        let target_offset = target_source.find("a.next").unwrap() + "a.".len();

        let location = definition_for_source(
            &entry,
            source,
            position,
            &crate::StdSourceOptions {
                std_root: Some(std_root),
            },
        )
        .unwrap();

        assert_eq!(location.uri, Url::from_file_path(&target).unwrap());
        assert_eq!(
            location.range,
            source_range_to_lsp_range(
                &target_source,
                SourceRange {
                    start: target_offset,
                    end: target_offset + "next".len(),
                },
            )
        );
    }

    #[test]
    fn references_for_source_reports_reference_locations() {
        let root = temp_root("references-reference-locations");
        std::fs::create_dir_all(root.join("lib").join("std")).unwrap();
        std::fs::write(root.join("lib").join("std.yu"), "mod prelude;\n").unwrap();
        std::fs::write(root.join("lib").join("std").join("prelude.yu"), "").unwrap();

        let entry = root.join("main.yu");
        let source = "my x: int = 1\nmy y = x\n";
        let locations = references_for_source(
            &entry,
            source.to_string(),
            Position {
                line: 1,
                character: 7,
            },
            true,
            &crate::StdSourceOptions {
                std_root: Some(root.join("lib")),
            },
        );

        assert_eq!(
            locations,
            vec![
                Location {
                    uri: Url::from_file_path(&entry).unwrap(),
                    range: Range {
                        start: Position {
                            line: 0,
                            character: 3
                        },
                        end: Position {
                            line: 0,
                            character: 4
                        },
                    },
                },
                Location {
                    uri: Url::from_file_path(&entry).unwrap(),
                    range: Range {
                        start: Position {
                            line: 1,
                            character: 7
                        },
                        end: Position {
                            line: 1,
                            character: 8
                        },
                    },
                },
            ]
        );
    }

    #[test]
    fn prepare_rename_for_source_reports_reference_range() {
        let root = temp_root("prepare-rename-reference-range");
        std::fs::create_dir_all(root.join("lib").join("std")).unwrap();
        std::fs::write(root.join("lib").join("std.yu"), "mod prelude;\n").unwrap();
        std::fs::write(root.join("lib").join("std").join("prelude.yu"), "").unwrap();

        let entry = root.join("main.yu");
        let source = "my x: int = 1\nmy y = x\n";
        let response = prepare_rename_for_source(
            &entry,
            source.to_string(),
            Position {
                line: 1,
                character: 7,
            },
            &crate::StdSourceOptions {
                std_root: Some(root.join("lib")),
            },
        )
        .unwrap();

        assert_eq!(
            response,
            PrepareRenameResponse::Range(Range {
                start: Position {
                    line: 1,
                    character: 7
                },
                end: Position {
                    line: 1,
                    character: 8
                },
            })
        );
    }

    #[test]
    fn rename_for_source_reports_workspace_edit() {
        let root = temp_root("rename-workspace-edit");
        std::fs::create_dir_all(root.join("lib").join("std")).unwrap();
        std::fs::write(root.join("lib").join("std.yu"), "mod prelude;\n").unwrap();
        std::fs::write(root.join("lib").join("std").join("prelude.yu"), "").unwrap();

        let entry = root.join("main.yu");
        let source = "my x: int = 1\nmy y = x\n";
        let edit = rename_for_source(
            &entry,
            source.to_string(),
            Position {
                line: 1,
                character: 7,
            },
            "renamed",
            &crate::StdSourceOptions {
                std_root: Some(root.join("lib")),
            },
        )
        .unwrap();
        let uri = Url::from_file_path(&entry).unwrap();
        let changes = edit.changes.unwrap();

        assert_eq!(
            changes.get(&uri),
            Some(&vec![
                TextEdit {
                    range: Range {
                        start: Position {
                            line: 0,
                            character: 3
                        },
                        end: Position {
                            line: 0,
                            character: 4
                        },
                    },
                    new_text: "renamed".to_string(),
                },
                TextEdit {
                    range: Range {
                        start: Position {
                            line: 1,
                            character: 7
                        },
                        end: Position {
                            line: 1,
                            character: 8
                        },
                    },
                    new_text: "renamed".to_string(),
                },
            ])
        );
    }

    #[test]
    fn rename_for_source_refuses_invalid_identifier() {
        let root = temp_root("rename-invalid-identifier");
        let entry = root.join("main.yu");
        let source = "my x: int = 1\nmy y = x\n";

        let edit = rename_for_source(
            &entry,
            source.to_string(),
            Position {
                line: 1,
                character: 7,
            },
            "my",
            &crate::StdSourceOptions {
                std_root: Some(root.join("missing-lib")),
            },
        );

        assert_eq!(edit, None);
    }

    #[test]
    fn hover_for_source_uses_std_route_before_local_fallback() {
        let source = concat!(
            "// Optional record fields make compact named arguments.\n",
            "\n",
            "my area({width = 1, height = 2}) = width * height\n",
            "\n",
            "area { width: 3 }\n",
            "area {}\n",
            "area { width: 3, height: 4 }\n",
            "\n",
            "my next_area({width = 2, height = width + 1}) = width * height\n",
            "\n",
            "next_area { width: 3 }\n",
        );
        let hover = hover_for_source(
            Path::new("main.yu"),
            source.to_string(),
            Position {
                line: 8,
                character: 4,
            },
            &crate::StdSourceOptions {
                std_root: Some(workspace_std_root()),
            },
        )
        .unwrap();

        let HoverContents::Markup(contents) = hover.contents else {
            panic!("expected markdown hover");
        };
        assert!(
            contents.value.contains("next_area: "),
            "expected next_area hover, got {:?}",
            contents.value
        );
        assert!(
            !contents.value.contains("next_area: never"),
            "std route must not be replaced by local-only fallback: {:?}",
            contents.value
        );
    }

    #[test]
    fn hover_for_source_falls_back_to_local_route_when_std_fails() {
        let root = temp_root("hover-local-fallback");
        let entry = root.join("main.yu");
        let source = "my x: int = 1\nmy y = x\n";
        let hover = hover_for_source(
            &entry,
            source.to_string(),
            Position {
                line: 1,
                character: 7,
            },
            &crate::StdSourceOptions {
                std_root: Some(root.join("missing-lib")),
            },
        )
        .unwrap();

        assert_eq!(
            hover.contents,
            HoverContents::Markup(MarkupContent {
                kind: MarkupKind::Markdown,
                value: "```yulang\nx: int\n```".to_string(),
            })
        );
    }

    #[test]
    fn definition_for_source_falls_back_to_local_route_when_std_fails() {
        let root = temp_root("definition-local-fallback");
        let entry = root.join("main.yu");
        let source = "my x: int = 1\nmy y = x\n";
        let location = definition_for_source(
            &entry,
            source.to_string(),
            Position {
                line: 1,
                character: 7,
            },
            &crate::StdSourceOptions {
                std_root: Some(root.join("missing-lib")),
            },
        )
        .unwrap();

        assert_eq!(location.uri, Url::from_file_path(&entry).unwrap());
        assert_eq!(
            location.range,
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
    }

    #[tokio::test]
    async fn diagnostics_timeout_guard_skips_busy_source_diagnostics() {
        let slots = Arc::new(Semaphore::new(1));
        let _occupied = slots.clone().try_acquire_owned().unwrap();

        let result = run_diagnostics_with_timeout(
            slots,
            PathBuf::from("main.yu"),
            "my x = 1\n".to_string(),
            crate::StdSourceOptions::default(),
        )
        .await;

        assert!(matches!(result, DiagnosticsRunResult::Busy), "{result:?}");
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

    fn workspace_std_root() -> PathBuf {
        PathBuf::from(env!("CARGO_MANIFEST_DIR"))
            .join("..")
            .join("..")
            .join("lib")
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
