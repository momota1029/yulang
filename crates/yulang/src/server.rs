use std::collections::HashMap;
use std::path::{Path, PathBuf};
use std::sync::{Arc, Mutex};
use std::time::Duration;

use tokio::sync::Semaphore;
use tower_lsp::lsp_types::*;
use tower_lsp::{Client, LanguageServer, LspService, Server};
use yulang_editor::diagnostics as editor_diagnostics;
use yulang_editor::hover as editor_hover;
use yulang_editor::semantic_tokens;
use yulang_editor::text as editor_text;

use crate::source::{SourceDiagnosticRelated, SourceTextAnalysis};
use crate::{
    DocCommentRenderWorker, SourceDefinition, SourceDiagnostic, SourceDiagnosticRelatedOrigin,
    SourceFileIdentity, SourceHover, SourceHoverDocumentationDraft, SourceLocation, SourceRange,
    SourceRename,
};

const LSP_ANALYSIS_TIMEOUT: Duration = Duration::from_secs(3);
const LSP_ANALYSIS_DEBOUNCE: Duration = Duration::from_millis(150);
const LSP_REQUEST_TIMEOUT: Duration = Duration::from_secs(5);
const LSP_HOVER_CONTENT_CHAR_LIMIT: usize = 1200;

struct Backend {
    client: Client,
    std_root: Option<PathBuf>,
    documents: Arc<Mutex<HashMap<Url, String>>>,
    analysis_versions: Arc<Mutex<HashMap<Url, u64>>>,
    request_cache: Arc<Mutex<HashMap<LspRequestCacheKey, LspRequestCacheValue>>>,
    analysis_slots: Arc<Semaphore>,
    request_slots: Arc<Semaphore>,
    doc_comment_render_worker: Option<DocCommentRenderWorker>,
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
    analysis
        .analyze()
        .diagnostics
        .into_iter()
        .filter_map(|diagnostic| {
            lsp_diagnostic_for_source_diagnostic(path, source, analysis, diagnostic)
        })
        .collect()
}

fn lsp_diagnostic_for_source_diagnostic(
    path: &Path,
    source: &str,
    analysis: &SourceTextAnalysis,
    diagnostic: SourceDiagnostic,
) -> Option<Diagnostic> {
    let diagnostic = editor_diagnostic_for_source_diagnostic(diagnostic);
    if diagnostic
        .file
        .as_ref()
        .is_some_and(|file| file != analysis.focus_file())
    {
        return None;
    }
    let EditorDiagnosticWithFiles {
        diagnostic,
        related_files,
        ..
    } = diagnostic;
    let message = diagnostic.message_with_label_and_hint();
    let root_has_implicit_prelude = analysis.root_has_implicit_prelude();
    let range = diagnostic.range;
    let severity = diagnostic.severity;
    let code = diagnostic.code;
    let related_diagnostics = diagnostic.related;
    let related = related_files
        .into_iter()
        .zip(related_diagnostics)
        .filter_map(|(file, related)| {
            Some(DiagnosticRelatedInformation {
                location: lsp_location_for_source_diagnostic_related(
                    path,
                    source,
                    analysis,
                    &file,
                    related.range,
                )?,
                message: related.message,
            })
        })
        .collect::<Vec<_>>();
    let related_information = (!related.is_empty()).then_some(related);
    Some(Diagnostic {
        range: range
            .map(|range| lsp_range_for_root_byte_range(source, range, root_has_implicit_prelude))
            .unwrap_or_else(|| {
                lsp_range_for_root_byte_range(
                    source,
                    visible_document_root_byte_range(source, root_has_implicit_prelude),
                    root_has_implicit_prelude,
                )
            }),
        severity: Some(lsp_diagnostic_severity(severity)),
        code: code.map(NumberOrString::String),
        source: Some("yulang".to_string()),
        message,
        related_information,
        ..Default::default()
    })
}

struct EditorDiagnosticWithFiles {
    file: Option<SourceFileIdentity>,
    diagnostic: editor_diagnostics::Diagnostic,
    related_files: Vec<SourceFileIdentity>,
}

fn editor_diagnostic_for_source_diagnostic(
    diagnostic: SourceDiagnostic,
) -> EditorDiagnosticWithFiles {
    let SourceDiagnostic {
        severity,
        code,
        label,
        file,
        range,
        message,
        hint,
        related,
    } = diagnostic;
    let (related_files, related) = related
        .into_iter()
        .map(editor_related_diagnostic_for_source_related)
        .unzip();
    EditorDiagnosticWithFiles {
        file,
        diagnostic: editor_diagnostics::Diagnostic {
            severity: editor_diagnostic_severity(severity),
            code,
            label,
            range: range.map(byte_range_for_source_range),
            message,
            hint,
            related,
        },
        related_files,
    }
}

fn editor_related_diagnostic_for_source_related(
    related: SourceDiagnosticRelated,
) -> (SourceFileIdentity, editor_diagnostics::RelatedDiagnostic) {
    let SourceDiagnosticRelated {
        message,
        file,
        range,
        origin,
    } = related;
    (
        file,
        editor_diagnostics::RelatedDiagnostic {
            message,
            range: byte_range_for_source_range(range),
            origin: origin.map(editor_related_origin_for_source_origin),
        },
    )
}

fn lsp_location_for_source_diagnostic_related(
    root_path: &Path,
    root_source: &str,
    analysis: &SourceTextAnalysis,
    file: &SourceFileIdentity,
    range: editor_text::ByteRange,
) -> Option<Location> {
    if file == analysis.focus_file() {
        return Some(Location {
            uri: Url::from_file_path(root_path).ok()?,
            range: lsp_range_for_root_byte_range(
                root_source,
                range,
                analysis.root_has_implicit_prelude(),
            ),
        });
    }

    let (path, source, range_offset) = analysis.source_file(file)?;
    let visible_source = source.get(range_offset..)?;
    let visible_range = editor_text::subtract_prefix_after_start(range, range_offset);
    Some(Location {
        uri: Url::from_file_path(path).ok()?,
        range: lsp_range_for_byte_range(visible_source, visible_range),
    })
}

fn editor_diagnostic_severity(
    severity: crate::SourceDiagnosticSeverity,
) -> editor_diagnostics::DiagnosticSeverity {
    match severity {
        crate::SourceDiagnosticSeverity::Error => editor_diagnostics::DiagnosticSeverity::Error,
    }
}

fn editor_related_origin_for_source_origin(
    origin: SourceDiagnosticRelatedOrigin,
) -> editor_diagnostics::RelatedOrigin {
    match origin {
        SourceDiagnosticRelatedOrigin::TypeAnnotation => {
            editor_diagnostics::RelatedOrigin::TypeAnnotation
        }
        SourceDiagnosticRelatedOrigin::Expression => editor_diagnostics::RelatedOrigin::Expression,
        SourceDiagnosticRelatedOrigin::ImplCandidate => {
            editor_diagnostics::RelatedOrigin::ImplCandidate
        }
    }
}

fn lsp_diagnostic_severity(severity: editor_diagnostics::DiagnosticSeverity) -> DiagnosticSeverity {
    match severity {
        editor_diagnostics::DiagnosticSeverity::Error => DiagnosticSeverity::ERROR,
    }
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

fn hover_draft_for_source(
    path: &Path,
    source: String,
    position: Position,
    options: &crate::StdSourceOptions,
) -> Option<LspHoverDraft> {
    let analysis = source_analysis_for_source(path, source.clone(), options).ok()?;
    hover_for_analysis(path, &source, &analysis, position)
}

#[cfg(test)]
fn hover_for_source(
    path: &Path,
    source: String,
    position: Position,
    options: &crate::StdSourceOptions,
) -> Option<Hover> {
    hover_draft_for_source(path, source, position, options).map(LspHoverDraft::into_static_hover)
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
    path: &Path,
    source: &str,
    analysis: &SourceTextAnalysis,
    position: Position,
) -> Option<LspHoverDraft> {
    if let Some(hover) = diagnostic_hover_for_analysis(path, source, analysis, position) {
        return Some(LspHoverDraft::Diagnostic(hover));
    }

    let byte_offset = position_to_byte_offset(source, position)?;
    let hover = analysis.hover(byte_offset)?;
    Some(LspHoverDraft::Source(lsp_hover_draft_for_source_hover(
        source,
        hover,
        analysis.root_has_implicit_prelude(),
    )))
}

fn diagnostic_hover_for_analysis(
    path: &Path,
    source: &str,
    analysis: &SourceTextAnalysis,
    position: Position,
) -> Option<Hover> {
    let diagnostics = diagnostics_for_analysis(path, source, analysis);
    let hovered_uri = Url::from_file_path(path).ok()?;
    let targets = diagnostics
        .iter()
        .map(|diagnostic| lsp_diagnostic_hover_target(diagnostic, &hovered_uri))
        .collect::<Vec<_>>();
    let selection =
        editor_hover::select_diagnostic_hover(&targets, lsp_position_to_utf16(position))?;
    let diagnostic = diagnostics.into_iter().nth(selection.diagnostic_index)?;
    Some(lsp_hover_for_diagnostic_at_range(
        diagnostic,
        lsp_range_from_utf16(selection.range),
        selection.related_index,
    ))
}

fn lsp_diagnostic_hover_target(
    diagnostic: &Diagnostic,
    hovered_uri: &Url,
) -> editor_hover::DiagnosticHoverTarget {
    editor_hover::DiagnosticHoverTarget {
        range: lsp_range_to_utf16(diagnostic.range),
        related: diagnostic
            .related_information
            .as_ref()
            .map(|related| {
                related
                    .iter()
                    .enumerate()
                    .filter(|(_, related)| &related.location.uri == hovered_uri)
                    .map(
                        |(related_index, related)| editor_hover::DiagnosticHoverRelatedTarget {
                            related_index,
                            range: lsp_range_to_utf16(related.location.range),
                        },
                    )
                    .collect()
            })
            .unwrap_or_default(),
    }
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

#[cfg(test)]
fn lsp_hover_for_source_hover(
    source: &str,
    hover: SourceHover,
    root_has_implicit_prelude: bool,
) -> Hover {
    lsp_hover_draft_for_source_hover(source, hover, root_has_implicit_prelude).into_static_hover()
}

#[derive(Debug, Clone)]
enum LspHoverDraft {
    Diagnostic(Hover),
    Source(LspSourceHoverDraft),
}

#[cfg(test)]
impl LspHoverDraft {
    fn into_static_hover(self) -> Hover {
        match self {
            Self::Diagnostic(hover) => hover,
            Self::Source(hover) => hover.into_static_hover(),
        }
    }
}

#[derive(Debug, Clone)]
struct LspSourceHoverDraft {
    range: Range,
    signature: String,
    documentation: Option<SourceHoverDocumentationDraft>,
}

impl LspSourceHoverDraft {
    #[cfg(test)]
    fn into_static_hover(self) -> Hover {
        self.into_hover_with_lazy_markdown(None)
    }

    fn into_hover_with_lazy_markdown(self, lazy_markdown: Option<String>) -> Hover {
        let fallback_markdown = self
            .documentation
            .as_ref()
            .map(|documentation| documentation.fallback_markdown.as_str());
        let documentation_markdown = lazy_markdown.as_deref().or(fallback_markdown);
        let value = lsp_hover_markdown_value(&self.signature, documentation_markdown);
        Hover {
            contents: HoverContents::Markup(MarkupContent {
                kind: MarkupKind::Markdown,
                value,
            }),
            range: Some(self.range),
        }
    }
}

async fn resolve_lsp_hover_draft(
    draft: LspHoverDraft,
    worker: Option<DocCommentRenderWorker>,
    deadline: tokio::time::Instant,
) -> Hover {
    let mut source_draft = match draft {
        LspHoverDraft::Diagnostic(hover) => return hover,
        LspHoverDraft::Source(source_draft) => source_draft,
    };
    let lazy_render_input = source_draft
        .documentation
        .as_mut()
        .and_then(|documentation| documentation.lazy_render_input.take());
    let lazy_markdown = match (worker, lazy_render_input) {
        (Some(worker), Some(input)) => {
            let handle = tokio::task::spawn_blocking(move || worker.render(input));
            match tokio::time::timeout_at(deadline, handle).await {
                Ok(Ok(Ok(markdown))) => Some(markdown),
                Ok(Ok(Err(_))) | Ok(Err(_)) | Err(_) => None,
            }
        }
        _ => None,
    };
    source_draft.into_hover_with_lazy_markdown(lazy_markdown)
}

fn lsp_hover_draft_for_source_hover(
    source: &str,
    hover: SourceHover,
    root_has_implicit_prelude: bool,
) -> LspSourceHoverDraft {
    LspSourceHoverDraft {
        range: lsp_range_for_root_source(source, hover.range, root_has_implicit_prelude),
        signature: lsp_hover_source_contents(&hover.contents),
        documentation: hover.documentation,
    }
}

fn lsp_hover_markdown_value(signature: &str, documentation_markdown: Option<&str>) -> String {
    let mut value = format!("```yulang\n{signature}\n```");
    if let Some(documentation) = documentation_markdown.filter(|doc| !doc.is_empty()) {
        value.push_str("\n\n");
        value.push_str(documentation);
    }
    value
}

fn lsp_hover_source_contents(contents: &str) -> String {
    let mut chars = contents.chars();
    // Public type formatting truncates structurally first; this cap is the final LSP payload guard.
    let mut out = chars
        .by_ref()
        .take(LSP_HOVER_CONTENT_CHAR_LIMIT)
        .collect::<String>();
    if chars.next().is_some() {
        out.push_str("\n...");
    }
    out
}

fn lsp_hover_for_diagnostic_at_range(
    diagnostic: Diagnostic,
    range: Range,
    hovered_related_index: Option<usize>,
) -> Hover {
    let mut value = String::new();
    let severity = diagnostic
        .severity
        .as_ref()
        .and_then(diagnostic_severity_label);
    let code = diagnostic.code.as_ref().and_then(diagnostic_code_string);
    if severity.is_some() || code.is_some() {
        value.push_str("**");
        if let Some(severity) = severity {
            value.push_str(severity);
        }
        if severity.is_some() && code.is_some() {
            value.push_str(" · ");
        }
        if let Some(code) = code {
            value.push_str(code);
        }
        value.push_str("**\n\n");
    }
    value.push_str(&diagnostic.message);
    if let Some(related) = diagnostic.related_information.as_ref() {
        for (related_index, related) in related.iter().enumerate() {
            value.push_str("\n\n- ");
            if Some(related_index) == hovered_related_index {
                value.push_str("**Hovered related note:** ");
            }
            value.push_str(&related.message);
            value.push_str(" — `");
            value.push_str(&diagnostic_related_location_label(&related.location));
            value.push('`');
        }
    }
    Hover {
        contents: HoverContents::Markup(MarkupContent {
            kind: MarkupKind::Markdown,
            value,
        }),
        range: Some(range),
    }
}

fn diagnostic_severity_label(severity: &DiagnosticSeverity) -> Option<&'static str> {
    if severity == &DiagnosticSeverity::ERROR {
        Some("Error")
    } else if severity == &DiagnosticSeverity::WARNING {
        Some("Warning")
    } else if severity == &DiagnosticSeverity::INFORMATION {
        Some("Information")
    } else if severity == &DiagnosticSeverity::HINT {
        Some("Hint")
    } else {
        None
    }
}

fn diagnostic_related_location_label(location: &Location) -> String {
    format!(
        "{}:{}:{}",
        location.uri,
        location.range.start.line.saturating_add(1),
        location.range.start.character.saturating_add(1),
    )
}

fn diagnostic_code_string(code: &NumberOrString) -> Option<&str> {
    match code {
        NumberOrString::String(code) => Some(code),
        NumberOrString::Number(_) => None,
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
    lsp_range_for_root_byte_range(
        source,
        byte_range_for_source_range(range),
        root_has_implicit_prelude,
    )
}

fn lsp_range_for_root_byte_range(
    source: &str,
    range: editor_text::ByteRange,
    root_has_implicit_prelude: bool,
) -> Range {
    if root_has_implicit_prelude {
        lsp_range_for_loaded_root_range(source, range)
    } else {
        lsp_range_for_byte_range(source, range)
    }
}

fn visible_document_root_byte_range(
    source: &str,
    root_has_implicit_prelude: bool,
) -> editor_text::ByteRange {
    let start = if root_has_implicit_prelude {
        crate::source::IMPLICIT_STD_SOURCE_PREFIX_LEN
    } else {
        0
    };
    editor_text::ByteRange {
        start,
        end: start + source.len(),
    }
}

fn lsp_range_for_loaded_root_range(source: &str, range: editor_text::ByteRange) -> Range {
    lsp_range_for_byte_range(
        source,
        editor_text::subtract_prefix_after_start(
            range,
            crate::source::IMPLICIT_STD_SOURCE_PREFIX_LEN,
        ),
    )
}

fn source_range_to_lsp_range(source: &str, range: SourceRange) -> Range {
    lsp_range_for_byte_range(source, byte_range_for_source_range(range))
}

#[cfg(test)]
fn compute_line_starts(source: &str) -> Vec<usize> {
    editor_text::compute_line_starts(source)
}

#[cfg(test)]
fn byte_offset_to_position(source: &str, line_starts: &[usize], offset: usize) -> Position {
    lsp_position_from_utf16(editor_text::byte_offset_to_utf16_position(
        source,
        line_starts,
        offset,
    ))
}

fn position_to_byte_offset(source: &str, position: Position) -> Option<usize> {
    editor_text::utf16_position_to_byte_offset(source, lsp_position_to_utf16(position))
}

fn lsp_range_for_byte_range(source: &str, range: editor_text::ByteRange) -> Range {
    lsp_range_from_utf16(editor_text::utf16_range_for_byte_range(source, range))
}

fn byte_range_for_source_range(range: SourceRange) -> editor_text::ByteRange {
    editor_text::ByteRange {
        start: range.start,
        end: range.end,
    }
}

fn lsp_position_from_utf16(position: editor_text::Utf16Position) -> Position {
    Position {
        line: position.line,
        character: position.character,
    }
}

fn lsp_position_to_utf16(position: Position) -> editor_text::Utf16Position {
    editor_text::Utf16Position {
        line: position.line,
        character: position.character,
    }
}

fn lsp_range_from_utf16(range: editor_text::Utf16Range) -> Range {
    Range {
        start: lsp_position_from_utf16(range.start),
        end: lsp_position_from_utf16(range.end),
    }
}

fn lsp_range_to_utf16(range: Range) -> editor_text::Utf16Range {
    editor_text::Utf16Range {
        start: lsp_position_to_utf16(range.start),
        end: lsp_position_to_utf16(range.end),
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
        // Source analysis and deferred doc rendering share the existing
        // request budget; the draft retains static bytes if rendering times out.
        let deadline = tokio::time::Instant::now() + LSP_REQUEST_TIMEOUT;
        let handle = tokio::task::spawn_blocking(move || {
            hover_draft_for_source(&path, source, position, &options)
        });
        let draft = match tokio::time::timeout_at(deadline, handle).await {
            Ok(Ok(draft)) => draft,
            Ok(Err(_)) | Err(_) => None,
        };
        let hover = match draft {
            Some(draft) => Some(
                resolve_lsp_hover_draft(draft, self.doc_comment_render_worker.clone(), deadline)
                    .await,
            ),
            None => None,
        };
        drop(permit);
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
    let doc_comment_render_worker = DocCommentRenderWorker::start().ok();
    let (service, socket) = LspService::new(move |client| Backend {
        client,
        std_root,
        documents: Arc::new(Mutex::new(HashMap::new())),
        analysis_versions: Arc::new(Mutex::new(HashMap::new())),
        request_cache: Arc::new(Mutex::new(HashMap::new())),
        analysis_slots: Arc::new(Semaphore::new(1)),
        request_slots: Arc::new(Semaphore::new(2)),
        doc_comment_render_worker,
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

    fn diagnostics_fixture(name: &str) -> &'static str {
        match name {
            "case_missing_scrutinee" => include_str!(
                "../../../tests/yulang/regressions/diagnostics/case_missing_scrutinee.yu"
            ),
            "case_missing_arm_pattern" => include_str!(
                "../../../tests/yulang/regressions/diagnostics/case_missing_arm_pattern.yu"
            ),
            "case_missing_arm_body" => include_str!(
                "../../../tests/yulang/regressions/diagnostics/case_missing_arm_body.yu"
            ),
            "catch_missing_scrutinee" => include_str!(
                "../../../tests/yulang/regressions/diagnostics/catch_missing_scrutinee.yu"
            ),
            "catch_raw_brace_scrutinee" => include_str!(
                "../../../tests/yulang/regressions/diagnostics/catch_raw_brace_scrutinee.yu"
            ),
            "catch_missing_arm_pattern" => include_str!(
                "../../../tests/yulang/regressions/diagnostics/catch_missing_arm_pattern.yu"
            ),
            "catch_missing_arm_body" => include_str!(
                "../../../tests/yulang/regressions/diagnostics/catch_missing_arm_body.yu"
            ),
            "missing_index_argument" => include_str!(
                "../../../tests/yulang/regressions/diagnostics/missing_index_argument.yu"
            ),
            "unresolved_method_error" => {
                include_str!("../../../tests/yulang/regressions/runtime/unresolved_method_error.yu")
            }
            "ambiguous_method_error" => {
                include_str!("../../../tests/yulang/regressions/runtime/ambiguous_method_error.yu")
            }
            _ => panic!("unknown diagnostics fixture: {name}"),
        }
    }

    fn cross_file_ambiguous_method_fixture(
        name: &str,
    ) -> (PathBuf, PathBuf, String, crate::StdSourceOptions) {
        let root = temp_root(name);
        std::fs::create_dir_all(root.join("lib").join("std")).unwrap();
        std::fs::write(root.join("lib").join("std.yu"), "mod prelude;\n").unwrap();
        std::fs::write(root.join("lib").join("std").join("prelude.yu"), "").unwrap();
        let entry = root.join("main.yu");
        let candidates = root.join("candidates.yu");
        std::fs::write(
            &candidates,
            concat!(
                "pub role R 'a:\n",
                "    our a.foo: int\n",
                "\n",
                "impl int: R:\n",
                "    our x.foo = 1\n",
                "\n",
                "impl int: R:\n",
                "    our x.foo = 2\n",
            ),
        )
        .unwrap();
        let source = concat!(
            "mod candidates;\n",
            "use candidates::*\n",
            "my unrelated_0 = 0\n",
            "my unrelated_1 = 1\n",
            "my unrelated_2 = 2\n",
            "my unrelated_3 = 3\n",
            "my unrelated_4 = 4\n",
            "my unrelated_5 = 5\n",
            "my unrelated_6 = 6\n",
            "1.foo\n",
        )
        .to_string();
        let options = crate::StdSourceOptions {
            std_root: Some(root.join("lib")),
        };
        (entry, candidates, source, options)
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
        let source = "\
struct point { x: int } with:
  our p.norm2 = p.x
my make(x) = { name: x }
my got = make(1).norm2
";
        let tokens = decode_tokens(semantic_tokens_for_source(source));
        let ty = token_type_index("type");
        let function = token_type_index("function");
        let property = token_type_index("property");

        assert_semantic_token_at(&tokens, source, source.find("point").unwrap(), "point", ty);
        assert_semantic_token_at(
            &tokens,
            source,
            source.find("make").unwrap(),
            "make",
            function,
        );
        assert_semantic_token_at(
            &tokens,
            source,
            source.rfind("make").unwrap(),
            "make",
            function,
        );
        assert_semantic_token_at(
            &tokens,
            source,
            source.rfind("norm2").unwrap(),
            "norm2",
            function,
        );
        assert_semantic_token_at(
            &tokens,
            source,
            source.find("name").unwrap(),
            "name",
            property,
        );
        assert_no_semantic_token_at(
            &tokens,
            source,
            source.rfind("norm2").unwrap(),
            "norm2",
            property,
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
    fn diagnostics_survive_leading_blank_and_comment_trivia() {
        let root = temp_root("diagnostic-leading-trivia");
        std::fs::create_dir_all(root.join("lib").join("std")).unwrap();
        std::fs::write(root.join("lib").join("std.yu"), "mod prelude;\n").unwrap();
        std::fs::write(root.join("lib").join("std").join("prelude.yu"), "").unwrap();

        let source = "\n// keep the diagnostic after leading trivia\nmy x: bool = 1\n";
        let diagnostics = diagnostics_for_source(
            &root.join("main.yu"),
            source.to_string(),
            &crate::StdSourceOptions {
                std_root: Some(root.join("lib")),
            },
        );

        assert_eq!(diagnostics.len(), 1, "{diagnostics:?}");
        let diagnostic = &diagnostics[0];
        assert_eq!(
            diagnostic.range,
            Range {
                start: Position {
                    line: 2,
                    character: 3
                },
                end: Position {
                    line: 2,
                    character: 4
                },
            }
        );
        assert!(
            diagnostic.message.contains("type mismatch"),
            "{diagnostics:?}"
        );
        assert_diagnostic_code(diagnostic, "yulang.type-mismatch");
        let related = diagnostic
            .related_information
            .as_ref()
            .expect("type mismatch should keep related ranges after leading trivia");
        assert_eq!(related.len(), 2, "{related:?}");
        assert_eq!(
            related[0].location.range,
            Range {
                start: Position {
                    line: 2,
                    character: 6
                },
                end: Position {
                    line: 2,
                    character: 10
                },
            }
        );
        assert_eq!(
            related[1].location.range,
            Range {
                start: Position {
                    line: 2,
                    character: 13
                },
                end: Position {
                    line: 2,
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
    fn diagnostics_keep_incomplete_source_parser_and_lowering_errors() {
        let root = temp_root("incomplete-source-diagnostics");
        std::fs::create_dir_all(root.join("lib").join("std")).unwrap();
        std::fs::write(root.join("lib").join("std.yu"), "mod prelude;\n").unwrap();
        std::fs::write(root.join("lib").join("std").join("prelude.yu"), "").unwrap();

        let source = "my x =\n";
        let diagnostics = diagnostics_for_source(
            &root.join("main.yu"),
            source.to_string(),
            &crate::StdSourceOptions {
                std_root: Some(root.join("lib")),
            },
        );

        assert_eq!(diagnostics.len(), 2, "{diagnostics:?}");
        assert_eq!(
            diagnostics[0].range,
            Range {
                start: Position {
                    line: 0,
                    character: 6
                },
                end: Position {
                    line: 0,
                    character: 6
                },
            }
        );
        assert!(
            diagnostics[0].message.contains("unexpected end of input"),
            "{diagnostics:?}"
        );
        assert_diagnostic_code(&diagnostics[0], "yulang.syntax");
        assert_eq!(
            diagnostics[1].range,
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
            diagnostics[1]
                .message
                .contains("x: binding `x` is missing a body expression"),
            "{diagnostics:?}"
        );
        assert!(
            diagnostics[1]
                .message
                .contains("hint: write a body expression after `=`"),
            "{diagnostics:?}"
        );
        assert_diagnostic_code(&diagnostics[1], "yulang.missing-local-binding-body");
    }

    #[test]
    fn diagnostics_use_missing_index_argument_range() {
        let source = diagnostics_fixture("missing_index_argument");
        let diagnostics = diagnostics_for_source(
            &PathBuf::from("missing_index_argument.yu"),
            source.to_string(),
            &crate::StdSourceOptions {
                std_root: Some(workspace_std_root()),
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
            diagnostics[0]
                .message
                .contains("index expression is missing an argument"),
            "{diagnostics:?}"
        );
        assert!(
            diagnostics[0]
                .message
                .contains("hint: write an index expression inside the brackets"),
            "{diagnostics:?}"
        );
        assert_diagnostic_code(&diagnostics[0], "yulang.missing-index-argument");
    }

    #[test]
    fn diagnostics_use_case_syntax_ranges() {
        let cases = [
            (
                "case_missing_scrutinee",
                "yulang.missing-case-scrutinee",
                Range {
                    start: Position {
                        line: 0,
                        character: 0,
                    },
                    end: Position {
                        line: 0,
                        character: 4,
                    },
                },
                "case expression is missing the value to inspect",
            ),
            (
                "case_missing_arm_pattern",
                "yulang.missing-case-arm-pattern",
                Range {
                    start: Position {
                        line: 1,
                        character: 2,
                    },
                    end: Position {
                        line: 1,
                        character: 4,
                    },
                },
                "case arm is missing a pattern",
            ),
            (
                "case_missing_arm_body",
                "yulang.missing-case-arm-body",
                Range {
                    start: Position {
                        line: 1,
                        character: 4,
                    },
                    end: Position {
                        line: 1,
                        character: 6,
                    },
                },
                "case arm is missing a body expression",
            ),
        ];

        for (fixture, code, range, message) in cases {
            let diagnostics = diagnostics_for_source(
                &PathBuf::from(format!("{fixture}.yu")),
                diagnostics_fixture(fixture).to_string(),
                &crate::StdSourceOptions::default(),
            );
            assert_eq!(diagnostics.len(), 1, "{fixture}: {diagnostics:?}");
            let diagnostic = &diagnostics[0];
            assert_eq!(diagnostic.range, range, "{fixture}: {diagnostics:?}");
            assert!(
                diagnostic.message.contains(message),
                "{fixture}: {diagnostics:?}"
            );
            assert_diagnostic_code(diagnostic, code);
        }
    }

    #[test]
    fn diagnostics_use_catch_syntax_ranges() {
        let root = temp_root("catch-syntax-ranges");
        std::fs::create_dir_all(root.join("lib").join("std")).unwrap();
        std::fs::write(root.join("lib").join("std.yu"), "mod prelude;\n").unwrap();
        std::fs::write(root.join("lib").join("std").join("prelude.yu"), "").unwrap();

        let cases = [
            (
                "catch_missing_scrutinee",
                "yulang.missing-catch-scrutinee",
                Range {
                    start: Position {
                        line: 0,
                        character: 0,
                    },
                    end: Position {
                        line: 0,
                        character: 5,
                    },
                },
                "catch expression is missing the computation to handle",
                "hint: write `catch <expr>:` before the handler arms",
            ),
            (
                "catch_raw_brace_scrutinee",
                "yulang.missing-catch-scrutinee",
                Range {
                    start: Position {
                        line: 0,
                        character: 0,
                    },
                    end: Position {
                        line: 0,
                        character: 5,
                    },
                },
                "catch expression is missing the computation to handle",
                "hint: write `catch <expr>:` before the handler arms",
            ),
            (
                "catch_missing_arm_pattern",
                "yulang.missing-catch-arm-pattern",
                Range {
                    start: Position {
                        line: 1,
                        character: 4,
                    },
                    end: Position {
                        line: 1,
                        character: 6,
                    },
                },
                "catch arm is missing a value pattern or effect operation",
                "hint: write a value pattern or effect operation before `->`",
            ),
            (
                "catch_missing_arm_body",
                "yulang.missing-catch-arm-body",
                Range {
                    start: Position {
                        line: 1,
                        character: 10,
                    },
                    end: Position {
                        line: 1,
                        character: 12,
                    },
                },
                "catch arm is missing a body expression",
                "hint: write an expression after `->`",
            ),
        ];

        for (fixture, code, range, message, hint) in cases {
            let diagnostics = diagnostics_for_source(
                &root.join(format!("{fixture}.yu")),
                diagnostics_fixture(fixture).to_string(),
                &crate::StdSourceOptions {
                    std_root: Some(root.join("lib")),
                },
            );

            assert_eq!(diagnostics.len(), 1, "{fixture}: {diagnostics:?}");
            let diagnostic = &diagnostics[0];
            assert_eq!(diagnostic.range, range, "{fixture}");
            assert_eq!(
                diagnostic.severity,
                Some(DiagnosticSeverity::ERROR),
                "{fixture}"
            );
            assert!(
                diagnostic.message.contains(message),
                "{fixture}: {diagnostics:?}"
            );
            assert!(
                diagnostic.message.contains(hint),
                "{fixture}: {diagnostics:?}"
            );
            assert_eq!(diagnostic.related_information, None, "{fixture}");
            assert_diagnostic_code(diagnostic, code);
        }
    }

    #[test]
    fn diagnostics_use_role_method_ranges_and_related_candidates() {
        let unresolved_root = temp_root("lsp-unresolved-method-diagnostic");
        std::fs::create_dir_all(&unresolved_root).unwrap();
        let unresolved = diagnostics_for_source(
            &unresolved_root.join("unresolved_method_error.yu"),
            diagnostics_fixture("unresolved_method_error").to_string(),
            &crate::StdSourceOptions {
                std_root: Some(workspace_std_root()),
            },
        );

        assert_eq!(unresolved.len(), 1, "{unresolved:?}");
        let diagnostic = &unresolved[0];
        assert_eq!(
            diagnostic.range,
            Range {
                start: Position {
                    line: 0,
                    character: 10,
                },
                end: Position {
                    line: 0,
                    character: 14,
                },
            }
        );
        assert_eq!(diagnostic.severity, Some(DiagnosticSeverity::ERROR));
        assert!(
            diagnostic
                .message
                .contains("no role implementation satisfies this method call"),
            "{diagnostic:?}"
        );
        assert!(
            diagnostic.message.contains(
                "hint: add or import an impl for the receiver type, or call a method supported by that value"
            ),
            "{diagnostic:?}"
        );
        assert_eq!(diagnostic.related_information, None);
        assert_diagnostic_code(diagnostic, "yulang.unresolved-method");

        let ambiguous_root = temp_root("lsp-ambiguous-method-diagnostic");
        std::fs::create_dir_all(&ambiguous_root).unwrap();
        let ambiguous = diagnostics_for_source(
            &ambiguous_root.join("ambiguous_method_error.yu"),
            diagnostics_fixture("ambiguous_method_error").to_string(),
            &crate::StdSourceOptions::default(),
        );

        assert_eq!(ambiguous.len(), 1, "{ambiguous:?}");
        let diagnostic = &ambiguous[0];
        assert_eq!(
            diagnostic.range,
            Range {
                start: Position {
                    line: 9,
                    character: 2,
                },
                end: Position {
                    line: 9,
                    character: 5,
                },
            }
        );
        assert_eq!(diagnostic.severity, Some(DiagnosticSeverity::ERROR));
        assert!(
            diagnostic
                .message
                .contains("more than one role implementation satisfies this method call"),
            "{diagnostic:?}"
        );
        assert!(
            diagnostic
                .message
                .contains("hint: make the receiver type more specific"),
            "{diagnostic:?}"
        );
        let related = diagnostic
            .related_information
            .as_ref()
            .expect("ambiguous method should carry candidate impl related ranges");
        assert_eq!(related.len(), 2, "{related:?}");
        assert!(
            related
                .iter()
                .all(|item| item.message.contains("matching impl method candidate")),
            "{related:?}"
        );
        assert_diagnostic_code(diagnostic, "yulang.ambiguous-method");
    }

    #[test]
    fn diagnostics_resolve_cross_file_role_method_candidates() {
        let (entry, candidates, source, options) =
            cross_file_ambiguous_method_fixture("cross-file-ambiguous-method-diagnostic");
        let diagnostics = diagnostics_for_source(&entry, source, &options);

        assert_eq!(diagnostics.len(), 1, "{diagnostics:?}");
        let diagnostic = &diagnostics[0];
        assert_diagnostic_code(diagnostic, "yulang.ambiguous-method");
        let related = diagnostic
            .related_information
            .as_ref()
            .expect("ambiguous method should retain cross-file candidates");
        let candidates_uri = Url::from_file_path(candidates).unwrap();
        assert_eq!(related.len(), 2, "{related:?}");
        assert!(
            related
                .iter()
                .all(|item| item.location.uri == candidates_uri),
            "{related:?}"
        );
        assert!(
            related
                .iter()
                .all(|item| item.location.uri != Url::from_file_path(&entry).unwrap()),
            "{related:?}"
        );
    }

    #[test]
    fn diagnostics_without_primary_range_span_visible_document() {
        let root = temp_root("document-wide-diagnostic-range");
        std::fs::create_dir_all(root.join("lib").join("std")).unwrap();
        std::fs::write(root.join("lib").join("std.yu"), "mod prelude;\n").unwrap();
        std::fs::write(root.join("lib").join("std").join("prelude.yu"), "").unwrap();
        let entry = root.join("main.yu");
        let source = "my value = \"💡\"";
        let analysis = source_analysis_for_source(
            &entry,
            source.to_string(),
            &crate::StdSourceOptions {
                std_root: Some(root.join("lib")),
            },
        )
        .unwrap();
        assert!(analysis.root_has_implicit_prelude());

        let diagnostic = lsp_diagnostic_for_source_diagnostic(
            &entry,
            source,
            &analysis,
            SourceDiagnostic {
                severity: crate::SourceDiagnosticSeverity::Error,
                code: Some("yulang.document".to_string()),
                label: None,
                file: Some(analysis.focus_file().clone()),
                range: None,
                message: "document-wide diagnostic".to_string(),
                hint: None,
                related: Vec::new(),
            },
        )
        .unwrap();

        assert_eq!(
            diagnostic.range,
            Range {
                start: Position {
                    line: 0,
                    character: 0,
                },
                end: Position {
                    line: 0,
                    character: 15,
                },
            }
        );
    }

    #[test]
    fn diagnostics_drop_unresolvable_related_files() {
        let root = temp_root("unresolvable-related-diagnostic");
        let entry = root.join("main.yu");
        let source = "my value = 1\n";
        let analysis = source_analysis_for_source(
            &entry,
            source.to_string(),
            &crate::StdSourceOptions {
                std_root: Some(root.join("missing-lib")),
            },
        )
        .unwrap();
        let diagnostic = lsp_diagnostic_for_source_diagnostic(
            &entry,
            source,
            &analysis,
            SourceDiagnostic {
                severity: crate::SourceDiagnosticSeverity::Error,
                code: Some("yulang.test".to_string()),
                label: None,
                file: Some(analysis.focus_file().clone()),
                range: Some(SourceRange { start: 3, end: 8 }),
                message: "test diagnostic".to_string(),
                hint: None,
                related: vec![SourceDiagnosticRelated {
                    message: "missing related file".to_string(),
                    file: sources::Path {
                        segments: vec![sources::Name("missing".to_string())],
                    },
                    range: SourceRange { start: 0, end: 1 },
                    origin: None,
                }],
            },
        )
        .unwrap();

        assert_eq!(diagnostic.related_information, None, "{diagnostic:?}");
    }

    #[test]
    fn diagnostics_exclude_primary_locations_from_other_files() {
        let root = temp_root("cross-file-primary-diagnostic");
        std::fs::create_dir_all(root.join("lib").join("std")).unwrap();
        std::fs::write(root.join("lib").join("std.yu"), "mod prelude;\n").unwrap();
        std::fs::write(root.join("lib").join("std").join("prelude.yu"), "").unwrap();
        std::fs::write(root.join("child.yu"), "my broken: bool = 1\n").unwrap();
        let diagnostics = diagnostics_for_source(
            &root.join("main.yu"),
            "mod child;\nmy root = 1\n".to_string(),
            &crate::StdSourceOptions {
                std_root: Some(root.join("lib")),
            },
        );

        assert!(diagnostics.is_empty(), "{diagnostics:?}");
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
    fn hover_for_source_reports_effect_operation_at_reference() {
        let root = temp_root("hover-effect-operation-reference");
        std::fs::create_dir_all(root.join("lib").join("std")).unwrap();
        std::fs::write(root.join("lib").join("std.yu"), "mod prelude;\n").unwrap();
        std::fs::write(root.join("lib").join("std").join("prelude.yu"), "").unwrap();

        let source = "act choose:\n  our pick: int -> bool\nmy result = choose::pick 1\n";
        let hover = hover_for_source(
            &root.join("main.yu"),
            source.to_string(),
            Position {
                line: 2,
                character: 20,
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
                    line: 2,
                    character: 20,
                },
                end: Position {
                    line: 2,
                    character: 24,
                },
            })
        );
        assert_eq!(
            hover.contents,
            HoverContents::Markup(MarkupContent {
                kind: MarkupKind::Markdown,
                value: "```yulang\npick: int -> [choose] bool\n```".to_string(),
            })
        );
    }

    #[test]
    fn lsp_hover_for_source_hover_limits_large_payloads() {
        let source = "my x = 1\n";
        let long_type = format!("x: {}int", "int -> ".repeat(300));
        let hover = lsp_hover_for_source_hover(
            source,
            SourceHover {
                range: SourceRange { start: 3, end: 4 },
                contents: long_type,
                documentation: None,
            },
            false,
        );

        assert_eq!(
            hover.range,
            Some(Range {
                start: Position {
                    line: 0,
                    character: 3
                },
                end: Position {
                    line: 0,
                    character: 4
                },
            })
        );
        let HoverContents::Markup(contents) = hover.contents else {
            panic!("expected markdown hover");
        };
        assert!(
            contents.value.starts_with("```yulang\nx: int -> "),
            "{:?}",
            contents.value
        );
        assert!(
            contents.value.ends_with("\n...\n```"),
            "{:?}",
            contents.value
        );
        assert!(
            contents.value.chars().count()
                <= LSP_HOVER_CONTENT_CHAR_LIMIT + "```yulang\n\n...\n```".chars().count(),
            "{:?}",
            contents.value
        );
    }

    #[test]
    fn hover_for_source_reports_doc_comment_markdown_below_signature() {
        let root = temp_root("hover-doc-comment");
        std::fs::create_dir_all(root.join("lib").join("std")).unwrap();
        std::fs::write(root.join("lib").join("std.yu"), "mod prelude;\n").unwrap();
        std::fs::write(root.join("lib").join("std").join("prelude.yu"), "").unwrap();

        let source = "-- **documented** value\nmy x: int = 1\nmy y = x\n";
        let hover = hover_for_source(
            &root.join("main.yu"),
            source.to_string(),
            Position {
                line: 2,
                character: 7,
            },
            &crate::StdSourceOptions {
                std_root: Some(root.join("lib")),
            },
        )
        .unwrap();

        assert_eq!(
            hover.contents,
            HoverContents::Markup(MarkupContent {
                kind: MarkupKind::Markdown,
                value: "```yulang\nx: int\n```\n\n**documented** value\n\n".to_string(),
            })
        );
    }

    #[test]
    fn hover_for_source_reports_rich_doc_comment_markdown_below_signature() {
        let root = temp_root("hover-rich-doc-comment");
        std::fs::create_dir_all(root.join("lib").join("std")).unwrap();
        std::fs::write(root.join("lib").join("std.yu"), "mod prelude;\n").unwrap();
        std::fs::write(root.join("lib").join("std").join("prelude.yu"), "").unwrap();

        let source = concat!(
            "---\n",
            "# Title\n",
            "A *soft* doc.\n",
            "\n",
            "- item\n",
            "```text\n",
            "body\n",
            "```\n",
            "---\n",
            "my x: int = 1\n",
            "my y = x\n",
        );
        let hover = hover_for_source(
            &root.join("main.yu"),
            source.to_string(),
            Position {
                line: 10,
                character: 7,
            },
            &crate::StdSourceOptions {
                std_root: Some(root.join("lib")),
            },
        )
        .unwrap();

        assert_eq!(
            hover.contents,
            HoverContents::Markup(MarkupContent {
                kind: MarkupKind::Markdown,
                // Ordinary source blank lines separate paragraphs without
                // contributing an additional visible blank-line operation.
                value: concat!(
                    "```yulang\n",
                    "x: int\n",
                    "```\n\n",
                    "# Title\n\n",
                    "A *soft* doc.\n\n",
                    "- item\n\n",
                    "```text\n",
                    "body\n",
                    "```\n\n",
                )
                .to_string(),
            })
        );
    }

    #[test]
    fn source_hover_draft_preserves_legacy_static_bytes_for_safe_and_unsafe_docs() {
        let root = temp_root("hover-doc-draft-static-parity");
        std::fs::create_dir_all(root.join("lib").join("std")).unwrap();
        std::fs::write(root.join("lib").join("std.yu"), "mod prelude;\n").unwrap();
        std::fs::write(root.join("lib").join("std").join("prelude.yu"), "").unwrap();
        let options = crate::StdSourceOptions {
            std_root: Some(root.join("lib")),
        };
        let cases = [
            (
                "safe static doc",
                "-- **safe** docs\nmy x: int = 1\n",
                Position {
                    line: 1,
                    character: 3,
                },
                true,
                "```yulang\nx: int\n```\n\n**safe** docs\n\n",
            ),
            (
                "unsafe inline-expression doc",
                "-- ![alt](url)\nmy x: int = 1\n",
                Position {
                    line: 1,
                    character: 3,
                },
                false,
                "```yulang\nx: int\n```\n\n![alt](url)\n\n",
            ),
            (
                "unsafe delimiter doc",
                "-- before } after\nmy x: int = 1\n",
                Position {
                    line: 1,
                    character: 3,
                },
                false,
                "```yulang\nx: int\n```\n\nbefore } after\n\n",
            ),
        ];

        for (name, source, position, expects_lazy_input, expected_markdown) in cases {
            let draft = hover_draft_for_source(
                &root.join("main.yu"),
                source.to_string(),
                position,
                &options,
            )
            .unwrap_or_else(|| panic!("{name}: expected hover draft"));
            let LspHoverDraft::Source(source_draft) = draft else {
                panic!("{name}: expected source hover draft");
            };
            let documentation = source_draft
                .documentation
                .as_ref()
                .unwrap_or_else(|| panic!("{name}: expected documentation draft"));
            assert_eq!(
                documentation.lazy_render_input.is_some(),
                expects_lazy_input,
                "{name}"
            );

            let hover = LspHoverDraft::Source(source_draft).into_static_hover();
            assert_eq!(
                hover.contents,
                HoverContents::Markup(MarkupContent {
                    kind: MarkupKind::Markdown,
                    value: expected_markdown.to_string(),
                }),
                "{name}"
            );
        }
    }

    #[tokio::test]
    async fn safe_source_hover_uses_the_resident_lazy_worker_and_its_cache() {
        use std::sync::atomic::{AtomicUsize, Ordering};

        let calls = Arc::new(AtomicUsize::new(0));
        let renderer_calls = calls.clone();
        let worker =
            crate::yumark_render_worker::start_doc_comment_render_worker_for_test(4, move |_| {
                renderer_calls.fetch_add(1, Ordering::SeqCst);
                Ok("rendered by lazy worker\n\n".to_string())
            })
            .unwrap();
        let draft =
            source_hover_draft_fixture("hover-lazy-worker-cache", "-- safe docs\nmy x: int = 1\n");

        for _ in 0..2 {
            let hover = resolve_lsp_hover_draft(
                draft.clone(),
                Some(worker.clone()),
                tokio::time::Instant::now() + Duration::from_secs(1),
            )
            .await;
            assert_eq!(
                hover.contents,
                HoverContents::Markup(MarkupContent {
                    kind: MarkupKind::Markdown,
                    value: "```yulang\nx: int\n```\n\nrendered by lazy worker\n\n".to_string(),
                })
            );
        }
        assert_eq!(calls.load(Ordering::SeqCst), 1);
    }

    #[tokio::test]
    async fn unsafe_source_hovers_skip_the_lazy_worker() {
        use std::sync::atomic::{AtomicUsize, Ordering};

        let calls = Arc::new(AtomicUsize::new(0));
        let renderer_calls = calls.clone();
        let worker =
            crate::yumark_render_worker::start_doc_comment_render_worker_for_test(4, move |_| {
                renderer_calls.fetch_add(1, Ordering::SeqCst);
                Ok("must not render".to_string())
            })
            .unwrap();
        for (name, source) in [
            ("delimiter", "-- before } after\nmy x: int = 1\n"),
            ("inline-expression", "-- ![alt](url)\nmy x: int = 1\n"),
            ("command", "-- \\cmd\nmy x: int = 1\n"),
        ] {
            let draft =
                source_hover_draft_fixture(&format!("hover-unsafe-skips-worker-{name}"), source);
            let expected = draft.clone().into_static_hover().contents;
            let hover = resolve_lsp_hover_draft(
                draft,
                Some(worker.clone()),
                tokio::time::Instant::now() + Duration::from_secs(1),
            )
            .await;

            assert_eq!(hover.contents, expected, "{name}");
        }
        assert_eq!(calls.load(Ordering::SeqCst), 0);
    }

    #[tokio::test]
    async fn lazy_worker_failure_or_unavailability_preserves_static_hover() {
        let worker =
            crate::yumark_render_worker::start_doc_comment_render_worker_for_test(4, |_| {
                Err(crate::YumarkLiteralEvaluationError::UnexpectedRootCount { actual: 0 })
            })
            .unwrap();
        let draft = source_hover_draft_fixture(
            "hover-lazy-worker-fallback",
            "-- **safe** docs\nmy x: int = 1\n",
        );
        let expected = HoverContents::Markup(MarkupContent {
            kind: MarkupKind::Markdown,
            value: "```yulang\nx: int\n```\n\n**safe** docs\n\n".to_string(),
        });

        let failed = resolve_lsp_hover_draft(
            draft.clone(),
            Some(worker),
            tokio::time::Instant::now() + Duration::from_secs(1),
        )
        .await;
        let unavailable = resolve_lsp_hover_draft(
            draft,
            None,
            tokio::time::Instant::now() + Duration::from_secs(1),
        )
        .await;

        assert_eq!(failed.contents, expected);
        assert_eq!(unavailable.contents, expected);
    }

    #[tokio::test]
    async fn lazy_worker_timeout_preserves_static_hover() {
        let worker =
            crate::yumark_render_worker::start_doc_comment_render_worker_for_test(4, |_| {
                std::thread::sleep(Duration::from_millis(25));
                Ok("late lazy output".to_string())
            })
            .unwrap();
        let draft = source_hover_draft_fixture(
            "hover-lazy-worker-timeout",
            "-- safe docs\nmy x: int = 1\n",
        );

        let hover = resolve_lsp_hover_draft(
            draft,
            Some(worker),
            tokio::time::Instant::now() + Duration::from_millis(1),
        )
        .await;

        assert_eq!(
            hover.contents,
            HoverContents::Markup(MarkupContent {
                kind: MarkupKind::Markdown,
                value: "```yulang\nx: int\n```\n\nsafe docs\n\n".to_string(),
            })
        );
    }

    #[test]
    fn hover_for_source_reports_eof_parser_diagnostic_at_empty_range() {
        let root = temp_root("hover-eof-parser-diagnostic");
        std::fs::create_dir_all(root.join("lib").join("std")).unwrap();
        std::fs::write(root.join("lib").join("std.yu"), "mod prelude;\n").unwrap();
        std::fs::write(root.join("lib").join("std").join("prelude.yu"), "").unwrap();

        let source = "my x = (1\n";
        let hover = hover_for_source(
            &root.join("main.yu"),
            source.to_string(),
            Position {
                line: 0,
                character: 9,
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
                    line: 0,
                    character: 9,
                },
                end: Position {
                    line: 0,
                    character: 9,
                },
            })
        );
        let HoverContents::Markup(contents) = hover.contents else {
            panic!("expected markdown hover");
        };
        assert!(contents.value.contains("yulang.syntax"), "{contents:?}");
        assert!(
            contents.value.contains("unexpected end of input"),
            "{contents:?}"
        );
    }

    #[test]
    fn hover_for_source_reports_diagnostic_summary_at_error_range() {
        let root = temp_root("hover-diagnostic-summary");
        std::fs::create_dir_all(root.join("lib").join("std")).unwrap();
        std::fs::write(root.join("lib").join("std.yu"), "mod prelude;\n").unwrap();
        std::fs::write(root.join("lib").join("std").join("prelude.yu"), "").unwrap();

        let source = "my x: bool = 1\n";
        let hover = hover_for_source(
            &root.join("main.yu"),
            source.to_string(),
            Position {
                line: 0,
                character: 3,
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
                    line: 0,
                    character: 3
                },
                end: Position {
                    line: 0,
                    character: 4
                },
            })
        );
        let HoverContents::Markup(contents) = hover.contents else {
            panic!("expected markdown hover");
        };
        assert!(
            contents.value.contains("**Error · yulang.type-mismatch**"),
            "{:?}",
            contents.value
        );
        assert!(
            contents.value.contains("yulang.type-mismatch"),
            "{:?}",
            contents.value
        );
        assert!(
            contents.value.contains("type mismatch"),
            "{:?}",
            contents.value
        );
        assert!(
            contents
                .value
                .contains("expected type comes from this type annotation: bool"),
            "{:?}",
            contents.value
        );
        assert!(
            contents
                .value
                .contains("actual type comes from this expression: int"),
            "{:?}",
            contents.value
        );
    }

    #[test]
    fn hover_for_source_reports_diagnostic_summary_at_related_range() {
        let root = temp_root("hover-diagnostic-related-range");
        std::fs::create_dir_all(root.join("lib").join("std")).unwrap();
        std::fs::write(root.join("lib").join("std.yu"), "mod prelude;\n").unwrap();
        std::fs::write(root.join("lib").join("std").join("prelude.yu"), "").unwrap();

        let source = "my x: bool = 1\n";
        let hover = hover_for_source(
            &root.join("main.yu"),
            source.to_string(),
            Position {
                line: 0,
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
                    line: 0,
                    character: 6
                },
                end: Position {
                    line: 0,
                    character: 10
                },
            })
        );
        let HoverContents::Markup(contents) = hover.contents else {
            panic!("expected markdown hover");
        };
        assert!(
            contents.value.contains("**Error · yulang.type-mismatch**"),
            "{:?}",
            contents.value
        );
        assert!(
            contents.value.contains("yulang.type-mismatch"),
            "{:?}",
            contents.value
        );
        assert!(
            contents.value.contains("type mismatch"),
            "{:?}",
            contents.value
        );
        assert!(
            contents
                .value
                .contains("expected type comes from this type annotation: bool"),
            "{:?}",
            contents.value
        );
        assert!(
            contents
                .value
                .contains("actual type comes from this expression: int"),
            "{:?}",
            contents.value
        );
        assert!(
            contents.value.contains(
                "- **Hovered related note:** expected type comes from this type annotation: bool"
            ),
            "{:?}",
            contents.value
        );
        assert!(
            !contents.value.contains(
                "- **Hovered related note:** actual type comes from this expression: int"
            ),
            "{:?}",
            contents.value
        );
        assert!(
            contents.value.contains("main.yu:1:7`"),
            "{:?}",
            contents.value
        );
    }

    #[test]
    fn diagnostic_hover_markdown_shows_all_related_notes() {
        let uri = Url::parse("file:///tmp/main.yu").unwrap();
        let related_information = (0..4)
            .map(|index| DiagnosticRelatedInformation {
                location: Location {
                    uri: uri.clone(),
                    range: Range {
                        start: Position {
                            line: index,
                            character: index,
                        },
                        end: Position {
                            line: index,
                            character: index + 1,
                        },
                    },
                },
                message: format!("related note {}", index + 1),
            })
            .collect();
        let hover = lsp_hover_for_diagnostic_at_range(
            Diagnostic {
                range: Range::default(),
                severity: Some(DiagnosticSeverity::WARNING),
                code: Some(NumberOrString::String("yulang.test".to_string())),
                source: Some("yulang".to_string()),
                message: "test diagnostic".to_string(),
                related_information: Some(related_information),
                ..Default::default()
            },
            Range::default(),
            Some(3),
        );

        let HoverContents::Markup(contents) = hover.contents else {
            panic!("expected markdown hover");
        };
        assert!(
            contents.value.contains("**Warning · yulang.test**"),
            "{:?}",
            contents.value
        );
        for index in 1..=4 {
            assert!(
                contents.value.contains(&format!("related note {index}")),
                "{:?}",
                contents.value
            );
        }
        assert!(
            contents
                .value
                .contains("- **Hovered related note:** related note 4"),
            "{:?}",
            contents.value
        );
        assert!(
            contents.value.contains("file:///tmp/main.yu:4:4`"),
            "{:?}",
            contents.value
        );
    }

    #[test]
    fn hover_for_source_reports_diagnostic_summary_after_leading_trivia() {
        let root = temp_root("hover-diagnostic-leading-trivia");
        std::fs::create_dir_all(root.join("lib").join("std")).unwrap();
        std::fs::write(root.join("lib").join("std.yu"), "mod prelude;\n").unwrap();
        std::fs::write(root.join("lib").join("std").join("prelude.yu"), "").unwrap();

        let source = "\n// keep hover on the user diagnostic line\nmy x: bool = 1\n";
        let hover = hover_for_source(
            &root.join("main.yu"),
            source.to_string(),
            Position {
                line: 2,
                character: 3,
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
                    line: 2,
                    character: 3
                },
                end: Position {
                    line: 2,
                    character: 4
                },
            })
        );
        let HoverContents::Markup(contents) = hover.contents else {
            panic!("expected markdown hover");
        };
        assert!(
            contents.value.contains("yulang.type-mismatch"),
            "{:?}",
            contents.value
        );
        assert!(
            contents
                .value
                .contains("expected type comes from this type annotation: bool"),
            "{:?}",
            contents.value
        );
        assert!(
            contents
                .value
                .contains("actual type comes from this expression: int"),
            "{:?}",
            contents.value
        );
    }

    #[test]
    fn hover_for_source_reports_diagnostic_summary_at_related_range_after_leading_trivia() {
        let root = temp_root("hover-diagnostic-related-leading-trivia");
        std::fs::create_dir_all(root.join("lib").join("std")).unwrap();
        std::fs::write(root.join("lib").join("std.yu"), "mod prelude;\n").unwrap();
        std::fs::write(root.join("lib").join("std").join("prelude.yu"), "").unwrap();

        let source = "\n// keep hover on the related user diagnostic line\nmy x: bool = 1\n";
        let hover = hover_for_source(
            &root.join("main.yu"),
            source.to_string(),
            Position {
                line: 2,
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
                    line: 2,
                    character: 6
                },
                end: Position {
                    line: 2,
                    character: 10
                },
            })
        );
        let HoverContents::Markup(contents) = hover.contents else {
            panic!("expected markdown hover");
        };
        assert!(
            contents.value.contains("yulang.type-mismatch"),
            "{:?}",
            contents.value
        );
        assert!(
            contents
                .value
                .contains("expected type comes from this type annotation: bool"),
            "{:?}",
            contents.value
        );
        assert!(
            contents
                .value
                .contains("actual type comes from this expression: int"),
            "{:?}",
            contents.value
        );
    }

    #[test]
    fn hover_for_source_reports_catch_diagnostic_summary() {
        let root = temp_root("hover-catch-diagnostic-summary");
        std::fs::create_dir_all(root.join("lib").join("std")).unwrap();
        std::fs::write(root.join("lib").join("std.yu"), "mod prelude;\n").unwrap();
        std::fs::write(root.join("lib").join("std").join("prelude.yu"), "").unwrap();

        let hover = hover_for_source(
            &root.join("main.yu"),
            diagnostics_fixture("catch_missing_arm_body").to_string(),
            Position {
                line: 1,
                character: 10,
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
                    character: 10
                },
                end: Position {
                    line: 1,
                    character: 12
                },
            })
        );
        let HoverContents::Markup(contents) = hover.contents else {
            panic!("expected markdown hover");
        };
        assert!(
            contents.value.contains("yulang.missing-catch-arm-body"),
            "{:?}",
            contents.value
        );
        assert!(
            contents
                .value
                .contains("catch arm is missing a body expression"),
            "{:?}",
            contents.value
        );
        assert!(
            contents
                .value
                .contains("hint: write an expression after `->`"),
            "{:?}",
            contents.value
        );
    }

    #[test]
    fn hover_for_source_reports_unresolved_role_method_diagnostic_summary() {
        let root = temp_root("hover-unresolved-role-method-diagnostic-summary");
        let source = diagnostics_fixture("unresolved_method_error");
        let method_offset = source.find("show").unwrap();
        let line_starts = compute_line_starts(source);

        let hover = hover_for_source(
            &root.join("main.yu"),
            source.to_string(),
            byte_offset_to_position(source, &line_starts, method_offset + 1),
            &crate::StdSourceOptions {
                std_root: Some(workspace_std_root()),
            },
        )
        .unwrap();

        assert_eq!(
            hover.range,
            Some(source_range_to_lsp_range(
                source,
                SourceRange {
                    start: method_offset,
                    end: method_offset + "show".len()
                }
            ))
        );
        let HoverContents::Markup(contents) = hover.contents else {
            panic!("expected markdown hover");
        };
        assert!(
            contents.value.contains("yulang.unresolved-method"),
            "{:?}",
            contents.value
        );
        assert!(
            contents
                .value
                .contains("show: no role implementation satisfies this method call for receiver"),
            "{:?}",
            contents.value
        );
        assert!(
            contents
                .value
                .contains("hint: add or import an impl for the receiver type"),
            "{:?}",
            contents.value
        );
    }

    #[test]
    fn hover_for_source_reports_ambiguous_role_method_candidates() {
        let root = temp_root("hover-ambiguous-role-method-candidates");
        let source = diagnostics_fixture("ambiguous_method_error");
        let method_offset = source.rfind("foo").unwrap();
        let line_starts = compute_line_starts(source);

        let hover = hover_for_source(
            &root.join("main.yu"),
            source.to_string(),
            byte_offset_to_position(source, &line_starts, method_offset + 1),
            &crate::StdSourceOptions::default(),
        )
        .unwrap();

        assert_eq!(
            hover.range,
            Some(source_range_to_lsp_range(
                source,
                SourceRange {
                    start: method_offset,
                    end: method_offset + "foo".len()
                }
            ))
        );
        let HoverContents::Markup(contents) = hover.contents else {
            panic!("expected markdown hover");
        };
        assert!(
            contents.value.contains("yulang.ambiguous-method"),
            "{:?}",
            contents.value
        );
        assert!(
            contents
                .value
                .contains("foo: more than one role implementation satisfies this method call"),
            "{:?}",
            contents.value
        );
        assert!(
            contents.value.contains("matching impl method candidate"),
            "{:?}",
            contents.value
        );
    }

    #[test]
    fn hover_ignores_cross_file_related_ranges_in_current_document() {
        let (entry, _, source, options) =
            cross_file_ambiguous_method_fixture("cross-file-related-hover");
        let diagnostics = diagnostics_for_source(&entry, source.clone(), &options);
        let related_position = diagnostics[0].related_information.as_ref().unwrap()[0]
            .location
            .range
            .start;

        let hover = hover_for_source(&entry, source, related_position, &options);
        if let Some(hover) = hover {
            let HoverContents::Markup(contents) = hover.contents else {
                panic!("expected markdown hover");
            };
            assert!(
                !contents.value.contains("yulang.ambiguous-method")
                    && !contents.value.contains("matching impl method candidate"),
                "cross-file related range triggered diagnostic hover: {:?}",
                contents.value
            );
        }
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

    fn source_hover_draft_fixture(name: &str, source: &str) -> LspHoverDraft {
        let root = temp_root(name);
        std::fs::create_dir_all(root.join("lib").join("std")).unwrap();
        std::fs::write(root.join("lib").join("std.yu"), "mod prelude;\n").unwrap();
        std::fs::write(root.join("lib").join("std").join("prelude.yu"), "").unwrap();
        let binding_line = source
            .lines()
            .position(|line| line.starts_with("my x:"))
            .expect("source fixture should contain the hovered binding");
        hover_draft_for_source(
            &root.join("main.yu"),
            source.to_string(),
            Position {
                line: binding_line as u32,
                character: 3,
            },
            &crate::StdSourceOptions {
                std_root: Some(root.join("lib")),
            },
        )
        .expect("source fixture should produce a hover draft")
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

    fn assert_semantic_token_at(
        tokens: &[(u32, u32, u32, u32)],
        source: &str,
        offset: usize,
        text: &str,
        token_type: u32,
    ) {
        let expected = semantic_token_tuple_at(source, offset, text, token_type);
        assert!(
            tokens.contains(&expected),
            "expected semantic token {expected:?}; got: {tokens:?}"
        );
    }

    fn assert_no_semantic_token_at(
        tokens: &[(u32, u32, u32, u32)],
        source: &str,
        offset: usize,
        text: &str,
        token_type: u32,
    ) {
        let unexpected = semantic_token_tuple_at(source, offset, text, token_type);
        assert!(
            !tokens.contains(&unexpected),
            "unexpected semantic token {unexpected:?}; got: {tokens:?}"
        );
    }

    fn semantic_token_tuple_at(
        source: &str,
        offset: usize,
        text: &str,
        token_type: u32,
    ) -> (u32, u32, u32, u32) {
        assert_eq!(&source[offset..offset + text.len()], text);
        let line_starts = compute_line_starts(source);
        let position = byte_offset_to_position(source, &line_starts, offset);
        (
            position.line,
            position.character,
            text.encode_utf16().count() as u32,
            token_type,
        )
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
