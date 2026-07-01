use std::cell::RefCell;
use std::collections::HashMap;
use std::fmt;

use parser::sink::YulangLanguage;
use poly::expr::{Def, Vis};
use poly::types::{Neg, Neu, Pos, StackWeight, Subtractability};
use rowan::SyntaxNode;
use serde::Serialize;
use wasm_bindgen::prelude::*;
use yulang_editor::semantic_tokens;

const PLAYGROUND_ENTRY: &str = "playground.yu";
const PLAYGROUND_STD_ARTIFACT_ENTRY: &str = "<embedded-playground-std-root>";
const FULL_STD_ARTIFACT_ENTRY: &str = "<embedded-std-root>";
const EMBEDDED_PLAYGROUND_STD_ARTIFACT: &[u8] =
    include_bytes!(concat!(env!("OUT_DIR"), "/embedded_playground_std.yucu"));
const EMBEDDED_FULL_STD_ARTIFACT: &[u8] =
    include_bytes!(concat!(env!("OUT_DIR"), "/embedded_full_std.yucu"));

thread_local! {
    static RUN_CACHE: RefCell<HashMap<String, RunOutput>> = RefCell::new(HashMap::new());
    static PLAYGROUND_STD_ARTIFACT: RefCell<Option<Option<yulang::cache::CachedCompiledUnitArtifact>>> =
        const { RefCell::new(None) };
    static FULL_STD_ARTIFACT: RefCell<Option<Option<yulang::cache::CachedCompiledUnitArtifact>>> =
        const { RefCell::new(None) };
}

#[wasm_bindgen]
pub fn run(source: &str) -> JsValue {
    set_panic_hook();
    to_js_value(&run_inner(source))
}

#[wasm_bindgen]
pub fn check(source: &str) -> JsValue {
    set_panic_hook();
    to_js_value(&check_inner(source))
}

#[wasm_bindgen]
pub fn colorize(source: &str) -> JsValue {
    set_panic_hook();
    to_js_value(&colorize_inner(source))
}

#[wasm_bindgen]
pub fn warm_std_cache() -> JsValue {
    set_panic_hook();
    to_js_value(&warm_std_cache_inner())
}

#[wasm_bindgen]
pub fn clear_std_cache() {
    RUN_CACHE.with(|cache| cache.borrow_mut().clear());
}

#[wasm_bindgen]
pub fn embedded_std_compiled_unit_artifact_status() -> JsValue {
    set_panic_hook();
    to_js_value(&embedded_std_status_inner())
}

#[wasm_bindgen(js_name = dumpPoly)]
pub fn dump_poly(source: &str) -> JsValue {
    set_panic_hook();
    to_js_value(&dump_poly_inner(source))
}

#[wasm_bindgen(js_name = dumpMono)]
pub fn dump_mono(source: &str) -> JsValue {
    set_panic_hook();
    to_js_value(&dump_mono_inner(source))
}

#[wasm_bindgen(js_name = stdFileCount)]
pub fn std_file_count() -> usize {
    yulang::stdlib::embedded_std_files().len()
}

pub fn colorize_inner(source: &str) -> ColorizeOutput {
    let spans = colorize_with_playground_op_table(source)
        .unwrap_or_else(|| colorize_with_default_op_table(source));
    ColorizeOutput {
        ok: true,
        spans,
        diagnostics: Vec::new(),
        source_len: source.len(),
    }
}

fn colorize_with_playground_op_table(source: &str) -> Option<Vec<HighlightSpan>> {
    let root =
        yulang::load_source_text_with_embedded_playground_std(PLAYGROUND_ENTRY, source.to_owned())
            .ok()?
            .into_iter()
            .find(|file| file.module_path.segments.is_empty())?;
    if !root.source.ends_with(source) {
        return None;
    }
    let prefix_len = root.source.len().checked_sub(source.len())?;
    let root_node = SyntaxNode::<YulangLanguage>::new_root(root.cst);
    let encoded = semantic_tokens::compute_with_root_and_highlights(&root.source, &root_node, None);
    Some(semantic_highlight_spans(
        source,
        &root.source,
        prefix_len,
        &encoded,
    ))
}

fn colorize_with_default_op_table(source: &str) -> Vec<HighlightSpan> {
    let encoded = semantic_tokens::compute(source);
    semantic_highlight_spans(source, source, 0, &encoded)
}

fn semantic_highlight_spans(
    source: &str,
    parsed_source: &str,
    source_offset_bytes: usize,
    encoded: &[u32],
) -> Vec<HighlightSpan> {
    let line_starts = line_utf16_starts(parsed_source);
    let source_offset = parsed_source[..source_offset_bytes.min(parsed_source.len())]
        .encode_utf16()
        .count();
    let source_len = source.encode_utf16().count();
    let mut line = 0usize;
    let mut col = 0usize;
    let mut spans = Vec::new();

    for chunk in encoded.chunks_exact(5) {
        let delta_line = chunk[0] as usize;
        let delta_col = chunk[1] as usize;
        line += delta_line;
        if delta_line == 0 {
            col += delta_col;
        } else {
            col = delta_col;
        }

        let Some(line_start) = line_starts.get(line).copied() else {
            continue;
        };
        let Some(kind) = highlight_kind_from_token_type(chunk[3]) else {
            continue;
        };
        let start = line_start + col;
        let end = start + chunk[2] as usize;
        if start < source_offset || end <= source_offset {
            continue;
        }
        let start = start - source_offset;
        let end = end - source_offset;
        if source_len < start || source_len < end {
            continue;
        }
        spans.push(HighlightSpan { start, end, kind });
    }

    spans
}

pub fn warm_std_cache_inner() -> WarmupOutput {
    let status = embedded_std_status_inner();
    WarmupOutput {
        source_cache_hits: 0,
        source_cache_misses: 0,
        source_cache_clone_ms: 0.0,
        source_cache_build_ms: 0.0,
        embedded_std_artifacts: status.artifacts,
        embedded_std_runtime_bindings: status.runtime_bindings,
        embedded_std_artifacts_bytes: status.bytes,
        embedded_std_artifacts_valid: status.valid,
        embedded_std_artifacts_fallback_reason: status.fallback_reason,
        total_ms: 0.0,
    }
}

pub fn embedded_std_status_inner() -> EmbeddedStdArtifactsOutput {
    let playground = embedded_playground_std_artifact();
    let full = embedded_full_std_artifact();
    let valid = playground.is_some() && full.is_some();
    EmbeddedStdArtifactsOutput {
        artifacts: usize::from(playground.is_some()) + usize::from(full.is_some()),
        runtime_bindings: 0,
        bytes: EMBEDDED_PLAYGROUND_STD_ARTIFACT.len() + EMBEDDED_FULL_STD_ARTIFACT.len(),
        valid,
        fallback_reason: (!valid).then(|| "embedded std artifact failed validation".to_string()),
    }
}

pub fn run_inner(source: &str) -> RunOutput {
    let cached = RUN_CACHE.with(|cache| cache.borrow().get(source).cloned());
    if let Some(mut output) = cached {
        if let Some(timings) = output.timings.as_mut() {
            timings.source_cache_hits += 1;
        }
        return output;
    }

    let output = run_inner_uncached(source);
    RUN_CACHE.with(|cache| {
        cache
            .borrow_mut()
            .insert(source.to_string(), output.clone());
    });
    output
}

pub fn check_inner(source: &str) -> CheckOutput {
    match yulang::check_poly_from_source_text_with_embedded_std(PLAYGROUND_ENTRY, source) {
        Ok(output) => {
            let diagnostics = output
                .diagnostics
                .iter()
                .map(|diagnostic| Diagnostic::from_source_diagnostic(diagnostic, source.len()))
                .collect::<Vec<_>>();
            CheckOutput {
                ok: diagnostics.is_empty(),
                file_count: output.file_count,
                text: output.text,
                diagnostics,
            }
        }
        Err(error) => CheckOutput::from_error(error.to_string(), source.len()),
    }
}

pub fn dump_poly_inner(source: &str) -> DumpOutput {
    match yulang::dump_poly_from_source_text_with_embedded_std(PLAYGROUND_ENTRY, source) {
        Ok(output) => DumpOutput::from_dump(output.file_count, output.text, output.errors, source),
        Err(error) => DumpOutput::from_error(error.to_string(), source.len()),
    }
}

pub fn dump_mono_inner(source: &str) -> DumpOutput {
    match yulang::dump_mono_from_source_text_with_embedded_std(PLAYGROUND_ENTRY, source) {
        Ok(output) => DumpOutput::from_dump(output.file_count, output.text, output.errors, source),
        Err(error) => DumpOutput::from_error(error.to_string(), source.len()),
    }
}

fn run_inner_uncached(source: &str) -> RunOutput {
    match run_evidence_from_source_text_without_std(source) {
        Ok(output) if output.errors.is_empty() => {
            return RunOutput::from_runtime_output(output, source, false);
        }
        Ok(output) if should_retry_with_embedded_std(source, &output.errors) => {
            return run_with_embedded_std_fallback(source, None);
        }
        Ok(output) => return RunOutput::from_runtime_output(output, source, false),
        Err(_) if source_likely_needs_embedded_std(source) => {
            return run_with_embedded_std_fallback(source, None);
        }
        Err(no_std_error) => {
            return run_with_embedded_std_fallback(source, Some(no_std_error));
        }
    }
}

fn run_with_embedded_std_fallback(
    source: &str,
    no_std_error: Option<WasmRuntimeError>,
) -> RunOutput {
    match run_evidence_from_source_text_with_playground_std(source) {
        Ok(output) if output.errors.is_empty() => {
            return RunOutput::from_runtime_output(output, source, true);
        }
        Ok(_) | Err(_) => {}
    }

    match run_evidence_from_source_text_with_embedded_std(source) {
        Ok(output) => RunOutput::from_runtime_output(output, source, true),
        Err(std_error) => {
            let message = match no_std_error {
                Some(no_std_error) => format!(
                    "{std_error}\n\nwithout embedded std, the earlier error was: {no_std_error}"
                ),
                None => std_error.to_string(),
            };
            RunOutput::from_error(message, source.len())
        }
    }
}

fn run_evidence_from_source_text_without_std(
    source: &str,
) -> Result<WasmRuntimeOutput, WasmRuntimeError> {
    let files = yulang::collect_local_source_text(PLAYGROUND_ENTRY, source.to_string())?;
    let output = build_named_runtime_from_collected_sources(files)?;
    run_built_evidence_program(output)
}

fn run_evidence_from_source_text_with_embedded_std(
    source: &str,
) -> Result<WasmRuntimeOutput, WasmRuntimeError> {
    let output = match embedded_full_std_artifact() {
        Some(artifact) => {
            let poly = yulang::build_poly_from_embedded_std_compiled_unit_artifact(
                artifact,
                source.to_string(),
            )?;
            build_named_runtime_from_poly(poly)?
        }
        None => {
            let files = yulang::collect_source_text_with_embedded_std(
                PLAYGROUND_ENTRY,
                source.to_string(),
            )?;
            build_named_runtime_from_collected_sources(files)?
        }
    };
    run_built_evidence_program(output)
}

fn run_evidence_from_source_text_with_playground_std(
    source: &str,
) -> Result<WasmRuntimeOutput, WasmRuntimeError> {
    let poly = match embedded_playground_std_artifact() {
        Some(artifact) => yulang::build_poly_from_embedded_playground_std_compiled_unit_artifact(
            artifact,
            source.to_string(),
        )?,
        None => yulang::build_poly_from_source_text_with_embedded_playground_std(
            PLAYGROUND_ENTRY,
            source.to_string(),
        )?,
    };
    let output = build_named_runtime_from_poly(poly)?;
    run_built_evidence_program(output)
}

fn embedded_playground_std_artifact() -> Option<yulang::cache::CachedCompiledUnitArtifact> {
    PLAYGROUND_STD_ARTIFACT.with(|cache| {
        if let Some(cached) = cache.borrow().as_ref() {
            return cached.clone();
        }

        let decoded = decode_embedded_playground_std_artifact();
        *cache.borrow_mut() = Some(decoded.clone());
        decoded
    })
}

fn embedded_full_std_artifact() -> Option<yulang::cache::CachedCompiledUnitArtifact> {
    FULL_STD_ARTIFACT.with(|cache| {
        if let Some(cached) = cache.borrow().as_ref() {
            return cached.clone();
        }

        let decoded = decode_embedded_full_std_artifact();
        *cache.borrow_mut() = Some(decoded.clone());
        decoded
    })
}

fn decode_embedded_playground_std_artifact() -> Option<yulang::cache::CachedCompiledUnitArtifact> {
    let files = yulang::collect_source_text_with_embedded_playground_std(
        PLAYGROUND_STD_ARTIFACT_ENTRY,
        String::new(),
    )
    .ok()?;
    let key = yulang::cache::source_cache_key(&files);
    let artifact =
        yulang::cache::decode_compiled_unit_artifact_bytes(EMBEDDED_PLAYGROUND_STD_ARTIFACT, key)
            .ok()
            .flatten()?;
    artifact.errors.is_empty().then_some(artifact)
}

fn decode_embedded_full_std_artifact() -> Option<yulang::cache::CachedCompiledUnitArtifact> {
    let files =
        yulang::collect_source_text_with_embedded_std(FULL_STD_ARTIFACT_ENTRY, String::new())
            .ok()?;
    let key = yulang::cache::source_cache_key(&files);
    let artifact =
        yulang::cache::decode_compiled_unit_artifact_bytes(EMBEDDED_FULL_STD_ARTIFACT, key)
            .ok()
            .flatten()?;
    artifact.errors.is_empty().then_some(artifact)
}

#[derive(Debug, Clone, PartialEq)]
struct NamedRuntimeBuild {
    output: yulang::BuildControlOutput,
    types: Vec<TypeResult>,
    display: PlaygroundDisplayContext,
}

fn build_named_runtime_from_collected_sources(
    files: Vec<yulang::CollectedSource>,
) -> Result<NamedRuntimeBuild, yulang::RouteError> {
    let poly = yulang::build_poly_from_collected_sources(files)?;
    build_named_runtime_from_poly(poly)
}

fn build_named_runtime_from_poly(
    poly: yulang::BuildPolyOutput,
) -> Result<NamedRuntimeBuild, yulang::RouteError> {
    let display = PlaygroundDisplayContext::from_poly(&poly);
    let types = exported_type_results(&poly, &display);
    let output = yulang::build_control_from_poly_output(&poly)?;
    Ok(NamedRuntimeBuild {
        output,
        types,
        display,
    })
}

fn exported_type_results(
    poly: &yulang::BuildPolyOutput,
    display: &PlaygroundDisplayContext,
) -> Vec<TypeResult> {
    poly.arena
        .roots
        .iter()
        .filter_map(|def| exported_type_result(poly, display, *def))
        .collect()
}

fn exported_type_result(
    poly: &yulang::BuildPolyOutput,
    display: &PlaygroundDisplayContext,
    def: poly::expr::DefId,
) -> Option<TypeResult> {
    let Def::Let {
        vis,
        scheme: Some(scheme),
        ..
    } = poly.arena.defs.get(def)?
    else {
        return None;
    };
    if !matches!(vis, Vis::Pub | Vis::Our) {
        return None;
    }
    let name = poly
        .labels
        .def_label(def)
        .map(str::to_string)
        .unwrap_or_else(|| format!("d{}", def.0));
    let ty = poly::dump::format_scheme_with_path_rewriter(&poly.arena.typ, scheme, &|path| {
        display.rewrite_type_path(path)
    });
    Some(TypeResult { name, ty })
}

fn run_built_evidence_program(
    build: NamedRuntimeBuild,
) -> Result<WasmRuntimeOutput, WasmRuntimeError> {
    let plan = evidence_vm::build_plan(&build.output.program, &build.output.runtime_evidence);
    let output = evidence_vm::run_program_with_plan(&build.output.program, &plan)?;
    let runtime_display = build.display.runtime_evidence_context();
    let results =
        output.root_value_texts_with_display_context(Some(&build.output.labels), &runtime_display);
    let text = output.roots_text_with_display_context(Some(&build.output.labels), &runtime_display);
    Ok(WasmRuntimeOutput {
        file_count: build.output.file_count,
        errors: build.output.errors,
        text,
        results,
        types: build.types,
        stdout: output.stdout,
        stats: output.evidence_stats,
    })
}

#[derive(Debug, Clone, Default, PartialEq, Eq)]
struct PlaygroundDisplayContext {
    constructors: HashMap<u32, String>,
    type_paths: ShortPathIndex,
}

impl PlaygroundDisplayContext {
    fn from_poly(poly: &yulang::BuildPolyOutput) -> Self {
        let constructor_paths = poly
            .arena
            .constructors
            .iter()
            .map(|(def, constructor)| (*def, constructor_full_path(constructor)))
            .collect::<Vec<_>>();
        let value_paths = ShortPathIndex::new(constructor_paths.iter().map(|(_, path)| path));
        let constructors = constructor_paths
            .into_iter()
            .map(|(def, path)| (def.0, value_paths.rewrite(&path).join("::")))
            .collect();

        let type_paths = ShortPathIndex::new(collect_type_display_paths(poly).iter());

        Self {
            constructors,
            type_paths,
        }
    }

    fn runtime_evidence_context(&self) -> evidence_vm::RuntimeEvidenceDisplayContext {
        let mut context = evidence_vm::RuntimeEvidenceDisplayContext::new();
        for (def, name) in &self.constructors {
            context.set_constructor_name_id(*def, name.clone());
        }
        context
    }

    fn rewrite_type_path(&self, path: &[String]) -> Vec<String> {
        self.type_paths.rewrite(path)
    }
}

#[derive(Debug, Clone, Default, PartialEq, Eq)]
struct ShortPathIndex {
    rewrites: HashMap<Vec<String>, Vec<String>>,
}

impl ShortPathIndex {
    fn new<'a>(paths: impl IntoIterator<Item = &'a Vec<String>>) -> Self {
        let mut unique_paths = paths
            .into_iter()
            .filter(|path| !path.is_empty())
            .cloned()
            .collect::<Vec<_>>();
        unique_paths.sort();
        unique_paths.dedup();

        let mut suffix_counts: HashMap<Vec<String>, usize> = HashMap::new();
        for path in &unique_paths {
            for start in 0..path.len() {
                *suffix_counts.entry(path[start..].to_vec()).or_default() += 1;
            }
        }

        let rewrites = unique_paths
            .into_iter()
            .map(|path| {
                let suffix = (0..path.len())
                    .rev()
                    .map(|start| path[start..].to_vec())
                    .find(|suffix| suffix_counts.get(suffix) == Some(&1))
                    .unwrap_or_else(|| path.clone());
                (path, suffix)
            })
            .collect();

        Self { rewrites }
    }

    fn rewrite(&self, path: &[String]) -> Vec<String> {
        self.rewrites
            .get(path)
            .cloned()
            .unwrap_or_else(|| path.to_vec())
    }
}

fn constructor_full_path(constructor: &poly::expr::Constructor) -> Vec<String> {
    let mut path = constructor.owner_path.clone();
    path.push(constructor.name.clone());
    path
}

fn collect_type_display_paths(poly: &yulang::BuildPolyOutput) -> Vec<Vec<String>> {
    let mut paths = Vec::new();
    for node in poly.arena.typ.pos_nodes() {
        collect_pos_type_paths(node, &mut paths);
    }
    for node in poly.arena.typ.neg_nodes() {
        collect_neg_type_paths(node, &mut paths);
    }
    for node in poly.arena.typ.neu_nodes() {
        collect_neu_type_paths(node, &mut paths);
    }
    for (_, def) in poly.arena.defs.iter() {
        if let Def::Let {
            scheme: Some(scheme),
            ..
        } = def
        {
            for predicate in &scheme.role_predicates {
                paths.push(predicate.role.clone());
            }
        }
    }
    paths
}

fn collect_pos_type_paths(node: &Pos, paths: &mut Vec<Vec<String>>) {
    match node {
        Pos::Con(path, _) => paths.push(path.clone()),
        Pos::Stack { weight, .. } | Pos::NonSubtract(_, weight) => {
            collect_stack_weight_paths(weight, paths);
        }
        _ => {}
    }
}

fn collect_neg_type_paths(node: &Neg, paths: &mut Vec<Vec<String>>) {
    match node {
        Neg::Con(path, _) => paths.push(path.clone()),
        Neg::Stack { weight, .. } => collect_stack_weight_paths(weight, paths),
        _ => {}
    }
}

fn collect_neu_type_paths(node: &Neu, paths: &mut Vec<Vec<String>>) {
    if let Neu::Con(path, _) = node {
        paths.push(path.clone());
    }
}

fn collect_stack_weight_paths(weight: &StackWeight, paths: &mut Vec<Vec<String>>) {
    collect_subtractability_paths(weight.filter_set(), paths);
    for entry in weight.entries() {
        for bound in entry.floor.iter().chain(entry.stack.iter()) {
            collect_subtractability_paths(bound, paths);
        }
    }
}

fn collect_subtractability_paths(value: &Subtractability, paths: &mut Vec<Vec<String>>) {
    match value {
        Subtractability::Empty | Subtractability::All => {}
        Subtractability::Set(path, _) | Subtractability::AllExcept(path, _) => {
            paths.push(path.clone());
        }
        Subtractability::SetMany(families) | Subtractability::AllExceptMany(families) => {
            paths.extend(families.iter().map(|(path, _)| path.clone()));
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
struct WasmRuntimeOutput {
    file_count: usize,
    errors: Vec<String>,
    text: String,
    results: Vec<String>,
    types: Vec<TypeResult>,
    stdout: String,
    stats: evidence_vm::RuntimeEvidenceRunStats,
}

#[derive(Debug)]
enum WasmRuntimeError {
    Route(yulang::RouteError),
    Runtime(evidence_vm::RuntimeEvidenceRunError),
}

impl From<yulang::RouteError> for WasmRuntimeError {
    fn from(error: yulang::RouteError) -> Self {
        Self::Route(error)
    }
}

impl From<evidence_vm::RuntimeEvidenceRunError> for WasmRuntimeError {
    fn from(error: evidence_vm::RuntimeEvidenceRunError) -> Self {
        Self::Runtime(error)
    }
}

impl fmt::Display for WasmRuntimeError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Route(error) => write!(f, "{error}"),
            Self::Runtime(error) => write!(f, "{error}"),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Serialize)]
pub struct RunOutput {
    pub ok: bool,
    pub file_count: usize,
    pub text: String,
    pub results: Vec<RunResult>,
    pub stdout: String,
    pub types: Vec<TypeResult>,
    pub timings: Option<RunTimings>,
    pub diagnostics: Vec<Diagnostic>,
    pub errors: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct RunResult {
    pub index: usize,
    pub value: String,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct TypeResult {
    pub name: String,
    pub ty: String,
}

#[derive(Debug, Clone, Copy, PartialEq, Serialize)]
pub struct RunTimings {
    pub vm_continuation_steps: usize,
    pub source_cache_hits: usize,
    pub source_cache_misses: usize,
    pub used_embedded_std: bool,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct CheckOutput {
    pub ok: bool,
    pub file_count: usize,
    pub text: String,
    pub diagnostics: Vec<Diagnostic>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct DumpOutput {
    pub ok: bool,
    pub file_count: usize,
    pub text: String,
    pub diagnostics: Vec<Diagnostic>,
    pub errors: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct Diagnostic {
    pub severity: DiagnosticSeverity,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub code: Option<String>,
    pub message: String,
    pub start: usize,
    pub end: usize,
    pub related: Vec<DiagnosticRelated>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub label: Option<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct DiagnosticRelated {
    pub message: String,
    pub start: usize,
    pub end: usize,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
#[serde(rename_all = "snake_case")]
pub enum DiagnosticSeverity {
    Error,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct ColorizeOutput {
    pub ok: bool,
    pub spans: Vec<HighlightSpan>,
    pub diagnostics: Vec<Diagnostic>,
    pub source_len: usize,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct HighlightSpan {
    pub start: usize,
    pub end: usize,
    pub kind: HighlightKind,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
#[serde(rename_all = "kebab-case")]
pub enum HighlightKind {
    Comment,
    Colon,
    Delimiter,
    Function,
    Keyword,
    Namespace,
    Number,
    Operator,
    Parameter,
    Pattern,
    Property,
    String,
    Type,
    TypeParameter,
}

#[derive(Debug, Clone, PartialEq, Serialize)]
pub struct WarmupOutput {
    pub source_cache_hits: usize,
    pub source_cache_misses: usize,
    pub source_cache_clone_ms: f64,
    pub source_cache_build_ms: f64,
    pub embedded_std_artifacts: usize,
    pub embedded_std_runtime_bindings: usize,
    pub embedded_std_artifacts_bytes: usize,
    pub embedded_std_artifacts_valid: bool,
    pub embedded_std_artifacts_fallback_reason: Option<String>,
    pub total_ms: f64,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct EmbeddedStdArtifactsOutput {
    pub artifacts: usize,
    pub runtime_bindings: usize,
    pub bytes: usize,
    pub valid: bool,
    pub fallback_reason: Option<String>,
}

impl RunOutput {
    fn from_runtime_output(
        output: WasmRuntimeOutput,
        source: &str,
        used_embedded_std: bool,
    ) -> Self {
        let diagnostics = diagnostics_from_messages(&output.errors, source.len());
        let results = output
            .results
            .into_iter()
            .enumerate()
            .map(|(index, value)| RunResult { index, value })
            .collect::<Vec<_>>();
        let vm_continuation_steps = evidence_vm_continuation_steps(&output.stats);
        Self {
            ok: diagnostics.is_empty(),
            file_count: output.file_count,
            text: output.text,
            results,
            stdout: output.stdout,
            types: output.types,
            timings: Some(RunTimings {
                vm_continuation_steps,
                source_cache_hits: 0,
                source_cache_misses: 1,
                used_embedded_std,
            }),
            diagnostics,
            errors: output.errors,
        }
    }

    fn from_error(message: String, source_len: usize) -> Self {
        Self {
            ok: false,
            file_count: 0,
            text: String::new(),
            results: Vec::new(),
            stdout: String::new(),
            types: Vec::new(),
            timings: Some(RunTimings {
                vm_continuation_steps: 0,
                source_cache_hits: 0,
                source_cache_misses: 1,
                used_embedded_std: false,
            }),
            diagnostics: vec![Diagnostic::error(message.clone(), source_len)],
            errors: vec![message],
        }
    }
}

fn evidence_vm_continuation_steps(stats: &evidence_vm::RuntimeEvidenceRunStats) -> usize {
    stats.continuation_append_steps
        + stats.continuation_resume_steps
        + stats.request_continuation_steps
}

impl CheckOutput {
    fn from_error(message: String, source_len: usize) -> Self {
        Self {
            ok: false,
            file_count: 0,
            text: String::new(),
            diagnostics: vec![Diagnostic::error(message, source_len)],
        }
    }
}

impl DumpOutput {
    fn from_dump(file_count: usize, text: String, errors: Vec<String>, source: &str) -> Self {
        let diagnostics = diagnostics_from_messages(&errors, source.len());
        Self {
            ok: diagnostics.is_empty(),
            file_count,
            text,
            diagnostics,
            errors,
        }
    }

    fn from_error(message: String, source_len: usize) -> Self {
        Self {
            ok: false,
            file_count: 0,
            text: String::new(),
            diagnostics: vec![Diagnostic::error(message.clone(), source_len)],
            errors: vec![message],
        }
    }
}

impl Diagnostic {
    fn error(message: String, source_len: usize) -> Self {
        Self {
            severity: DiagnosticSeverity::Error,
            code: None,
            message,
            start: 0,
            end: source_len,
            related: Vec::new(),
            label: None,
        }
    }

    fn from_source_diagnostic(diagnostic: &yulang::SourceDiagnostic, source_len: usize) -> Self {
        let (start, end) = diagnostic
            .range
            .map(|range| playground_diagnostic_range(range, source_len))
            .unwrap_or((0, source_len));
        Self {
            severity: DiagnosticSeverity::Error,
            code: diagnostic.code.clone(),
            message: diagnostic.message.clone(),
            start,
            end,
            related: diagnostic
                .related
                .iter()
                .map(|related| {
                    let (start, end) = playground_diagnostic_range(related.range, source_len);
                    DiagnosticRelated {
                        message: related.message.clone(),
                        start,
                        end,
                    }
                })
                .collect(),
            label: diagnostic.label.clone(),
        }
    }
}

fn playground_diagnostic_range(range: yulang::SourceRange, source_len: usize) -> (usize, usize) {
    let start = range
        .start
        .saturating_sub(yulang::IMPLICIT_STD_SOURCE_PREFIX_LEN)
        .min(source_len);
    let end = range
        .end
        .saturating_sub(yulang::IMPLICIT_STD_SOURCE_PREFIX_LEN)
        .min(source_len);
    if end < start {
        (start, start)
    } else {
        (start, end)
    }
}

fn diagnostics_from_messages(messages: &[String], source_len: usize) -> Vec<Diagnostic> {
    messages
        .iter()
        .cloned()
        .map(|message| Diagnostic::error(message, source_len))
        .collect()
}

fn source_likely_needs_embedded_std(source: &str) -> bool {
    source.contains("std::")
        || source.contains("use std")
        || source.contains('$')
        || source.contains(".list")
        || source.contains(".show")
        || source.contains(".map")
        || source.contains(".filter")
        || source.contains(".rev")
        || source.contains("for ")
        || source.contains("..")
        || source_has_identifier(source, "all")
        || source_has_identifier(source, "any")
}

fn should_retry_with_embedded_std(source: &str, errors: &[String]) -> bool {
    errors.iter().any(|error| {
        error.contains("unresolved value name")
            || error.contains("unresolved type name")
            || error.contains("UnresolvedName")
            || error.contains("UnresolvedTypeName")
            || error.contains("unsupported VM boundary") && source_likely_needs_embedded_std(source)
    })
}

fn source_has_identifier(source: &str, name: &str) -> bool {
    source
        .split(|ch: char| ch != '_' && !ch.is_ascii_alphanumeric())
        .any(|token| token == name)
}

fn highlight_kind_from_token_type(token_type: u32) -> Option<HighlightKind> {
    match token_type {
        0 => Some(HighlightKind::Function),
        1 => Some(HighlightKind::Type),
        2 => Some(HighlightKind::TypeParameter),
        3 => Some(HighlightKind::Namespace),
        4 => Some(HighlightKind::Parameter),
        5 => Some(HighlightKind::Keyword),
        6 => Some(HighlightKind::String),
        7 => Some(HighlightKind::Number),
        8 => Some(HighlightKind::Comment),
        9 => Some(HighlightKind::Operator),
        10 => Some(HighlightKind::Delimiter),
        11 => Some(HighlightKind::Colon),
        12 => Some(HighlightKind::Property),
        13 => Some(HighlightKind::Pattern),
        _ => None,
    }
}

fn line_utf16_starts(source: &str) -> Vec<usize> {
    let mut starts = vec![0];
    let mut offset = 0;
    for ch in source.chars() {
        offset += ch.len_utf16();
        if ch == '\n' {
            starts.push(offset);
        }
    }
    starts
}

fn to_js_value<T: Serialize>(value: &T) -> JsValue {
    serde_wasm_bindgen::to_value(value).unwrap_or_else(|error| {
        JsValue::from_str(&format!(
            "{{\"ok\":false,\"diagnostics\":[{{\"severity\":\"error\",\"message\":\"serialize wasm output: {error}\",\"start\":0,\"end\":0}}]}}"
        ))
    })
}

fn set_panic_hook() {
    #[cfg(target_arch = "wasm32")]
    console_error_panic_hook::set_once();
}

#[cfg(test)]
mod playground_tests;
