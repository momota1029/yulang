use std::cell::RefCell;
use std::collections::HashMap;

use parser::lex::SyntaxKind;
use parser::sink::YulangLanguage;
use rowan::{NodeOrToken, SyntaxNode};
use serde::Serialize;
use wasm_bindgen::prelude::*;

const PLAYGROUND_ENTRY: &str = "playground.yu";

thread_local! {
    static RUN_CACHE: RefCell<HashMap<String, RunOutput>> = RefCell::new(HashMap::new());
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
    let root = SyntaxNode::<YulangLanguage>::new_root(parser::parse_module_to_green(source));
    let spans = root
        .descendants_with_tokens()
        .filter_map(NodeOrToken::into_token)
        .filter_map(|token| {
            let kind = highlight_kind_for_syntax(token.kind())?;
            let range = token.text_range();
            Some(HighlightSpan {
                start: utf16_offset(source, usize::from(range.start())),
                end: utf16_offset(source, usize::from(range.end())),
                kind,
            })
        })
        .collect();
    ColorizeOutput {
        ok: true,
        spans,
        diagnostics: Vec::new(),
        source_len: source.len(),
    }
}

pub fn warm_std_cache_inner() -> WarmupOutput {
    WarmupOutput {
        source_cache_hits: 0,
        source_cache_misses: 0,
        source_cache_clone_ms: 0.0,
        source_cache_build_ms: 0.0,
        embedded_std_artifacts: yulang::stdlib::embedded_std_files().len(),
        embedded_std_runtime_bindings: 0,
        embedded_std_artifacts_bytes: embedded_std_source_bytes(),
        embedded_std_artifacts_valid: true,
        embedded_std_artifacts_fallback_reason: None,
        total_ms: 0.0,
    }
}

pub fn embedded_std_status_inner() -> EmbeddedStdArtifactsOutput {
    EmbeddedStdArtifactsOutput {
        artifacts: yulang::stdlib::embedded_std_files().len(),
        runtime_bindings: 0,
        bytes: embedded_std_source_bytes(),
        valid: true,
        fallback_reason: None,
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
    match run_control_from_source_text_without_std(source) {
        Ok(output) if output.errors.is_empty() => {
            return RunOutput::from_control_output(output, source, false);
        }
        Ok(output) if should_retry_with_embedded_std(&output.errors) => {
            return run_with_embedded_std_fallback(source, None);
        }
        Ok(output) => return RunOutput::from_control_output(output, source, false),
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
    no_std_error: Option<yulang::RouteError>,
) -> RunOutput {
    match run_control_from_source_text_with_playground_std(source) {
        Ok(output) if output.errors.is_empty() => {
            return RunOutput::from_control_output(output, source, true);
        }
        Ok(_) | Err(_) => {}
    }

    match run_control_from_source_text_with_embedded_std(source) {
        Ok(output) => RunOutput::from_control_output(output, source, true),
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

fn run_control_from_source_text_without_std(
    source: &str,
) -> Result<WasmControlOutput, yulang::RouteError> {
    let files = yulang::collect_local_source_text(PLAYGROUND_ENTRY, source.to_string())?;
    let output = yulang::build_control_from_collected_sources(files)?;
    run_built_control_program_with_host(output)
}

fn run_control_from_source_text_with_embedded_std(
    source: &str,
) -> Result<WasmControlOutput, yulang::RouteError> {
    let output =
        yulang::build_control_from_source_text_with_embedded_std(PLAYGROUND_ENTRY, source)?;
    run_built_control_program_with_host(output)
}

fn run_control_from_source_text_with_playground_std(
    source: &str,
) -> Result<WasmControlOutput, yulang::RouteError> {
    let output = yulang::build_control_from_source_text_with_embedded_playground_std(
        PLAYGROUND_ENTRY,
        source,
    )?;
    run_built_control_program_with_host(output)
}

fn run_built_control_program_with_host(
    output: yulang::BuildControlOutput,
) -> Result<WasmControlOutput, yulang::RouteError> {
    let mut stdout = String::new();
    let values = control_vm::run_program_with_host(&output.program, |path, payload| {
        handle_host_effect(path, payload, &mut stdout)
    })
    .map_err(yulang::RouteError::Control)?;
    Ok(WasmControlOutput {
        file_count: output.file_count,
        errors: output.errors,
        text: format!("run roots {}\n", control_vm::format_values(&values)),
        values,
        stdout,
    })
}

fn handle_host_effect(
    path: &[String],
    payload: &control_vm::Value,
    stdout: &mut String,
) -> Option<control_vm::Value> {
    if path == ["std", "io", "console", "out", "write"] {
        let text = host_string_payload(payload)?;
        stdout.push_str(text);
        return Some(control_vm::Value::Unit);
    }
    None
}

fn host_string_payload(value: &control_vm::Value) -> Option<&str> {
    match value {
        control_vm::Value::Str(value) => Some(value.as_str()),
        control_vm::Value::Marked { value, .. } => host_string_payload(value),
        _ => None,
    }
}

#[derive(Debug, Clone, PartialEq)]
struct WasmControlOutput {
    file_count: usize,
    errors: Vec<String>,
    text: String,
    values: Vec<control_vm::Value>,
    stdout: String,
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
    fn from_control_output(
        output: WasmControlOutput,
        source: &str,
        used_embedded_std: bool,
    ) -> Self {
        let diagnostics = diagnostics_from_messages(&output.errors, source.len());
        let results = output
            .values
            .iter()
            .enumerate()
            .map(|(index, value)| RunResult {
                index,
                value: format_control_value(value),
            })
            .collect::<Vec<_>>();
        Self {
            ok: diagnostics.is_empty(),
            file_count: output.file_count,
            text: output.text,
            results,
            stdout: output.stdout,
            types: Vec::new(),
            timings: Some(RunTimings {
                vm_continuation_steps: 0,
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
        Self {
            severity: DiagnosticSeverity::Error,
            code: None,
            message: diagnostic.message.clone(),
            start: 0,
            end: source_len,
            related: Vec::new(),
            label: diagnostic.label.clone(),
        }
    }
}

fn diagnostics_from_messages(messages: &[String], source_len: usize) -> Vec<Diagnostic> {
    messages
        .iter()
        .cloned()
        .map(|message| Diagnostic::error(message, source_len))
        .collect()
}

fn format_control_value(value: &control_vm::Value) -> String {
    let text = control_vm::format_values(std::slice::from_ref(value));
    text.strip_prefix('[')
        .and_then(|text| text.strip_suffix(']'))
        .unwrap_or(&text)
        .to_string()
}

fn embedded_std_source_bytes() -> usize {
    yulang::stdlib::embedded_std_files()
        .iter()
        .map(|file| file.source.len())
        .sum()
}

fn source_likely_needs_embedded_std(source: &str) -> bool {
    source.contains("std::")
        || source.contains("use std")
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

fn should_retry_with_embedded_std(errors: &[String]) -> bool {
    errors.iter().any(|error| {
        error.contains("unresolved value name")
            || error.contains("unresolved type name")
            || error.contains("UnresolvedName")
            || error.contains("UnresolvedTypeName")
    })
}

fn source_has_identifier(source: &str, name: &str) -> bool {
    source
        .split(|ch: char| ch != '_' && !ch.is_ascii_alphanumeric())
        .any(|token| token == name)
}

fn highlight_kind_for_syntax(kind: SyntaxKind) -> Option<HighlightKind> {
    match kind {
        SyntaxKind::LineComment
        | SyntaxKind::BlockComment
        | SyntaxKind::BlockCommentStart
        | SyntaxKind::BlockCommentText
        | SyntaxKind::BlockCommentEnd
        | SyntaxKind::DocComment => Some(HighlightKind::Comment),
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
        | SyntaxKind::Cast
        | SyntaxKind::Lazy
        | SyntaxKind::Infix
        | SyntaxKind::Prefix
        | SyntaxKind::Suffix
        | SyntaxKind::Nullfix => Some(HighlightKind::Keyword),
        SyntaxKind::Number => Some(HighlightKind::Number),
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
        | SyntaxKind::StringInterpCloseBrace
        | SyntaxKind::RuleLitStart
        | SyntaxKind::RuleLitEnd
        | SyntaxKind::RuleLitText
        | SyntaxKind::RuleLitOpenBrace
        | SyntaxKind::RuleLitCloseBrace
        | SyntaxKind::RuleLitColon
        | SyntaxKind::MarkLitStart
        | SyntaxKind::MarkLitEnd
        | SyntaxKind::MarkLitText
        | SyntaxKind::YmText => Some(HighlightKind::String),
        SyntaxKind::Symbol => Some(HighlightKind::Pattern),
        SyntaxKind::DotField => Some(HighlightKind::Property),
        SyntaxKind::OpName
        | SyntaxKind::Arrow
        | SyntaxKind::Equal
        | SyntaxKind::Pipe
        | SyntaxKind::Slash
        | SyntaxKind::DotDot
        | SyntaxKind::RuleQuantStar
        | SyntaxKind::RuleQuantStarLazy
        | SyntaxKind::RuleQuantPlus
        | SyntaxKind::RuleQuantPlusLazy
        | SyntaxKind::RuleQuantOpt
        | SyntaxKind::YadaYada => Some(HighlightKind::Operator),
        SyntaxKind::Colon => Some(HighlightKind::Colon),
        SyntaxKind::ParenL
        | SyntaxKind::ParenR
        | SyntaxKind::BracketL
        | SyntaxKind::BracketR
        | SyntaxKind::BraceL
        | SyntaxKind::BraceR
        | SyntaxKind::Backslash
        | SyntaxKind::Apostrophe
        | SyntaxKind::ColonColon
        | SyntaxKind::Comma
        | SyntaxKind::Semicolon
        | SyntaxKind::Tilde
        | SyntaxKind::Rule
        | SyntaxKind::YmHashSigil
        | SyntaxKind::YmHashDotSigil
        | SyntaxKind::YmListDashSigil
        | SyntaxKind::YmListNumSigil
        | SyntaxKind::YmFenceSigil
        | SyntaxKind::YmChevronBlockSigil
        | SyntaxKind::YmChevronPrefixSigil
        | SyntaxKind::YmLBracket
        | SyntaxKind::YmRBracket
        | SyntaxKind::YmBang
        | SyntaxKind::YmColon
        | SyntaxKind::YmBackslash
        | SyntaxKind::YmSemi
        | SyntaxKind::YmPrefix
        | SyntaxKind::YmStarSigil
        | SyntaxKind::YmStrongSigil
        | SyntaxKind::YmDocBlockSigil => Some(HighlightKind::Delimiter),
        _ => None,
    }
}

fn utf16_offset(source: &str, byte_offset: usize) -> usize {
    let byte_offset = byte_offset.min(source.len());
    source[..byte_offset].encode_utf16().count()
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
mod tests {
    use super::*;

    #[test]
    fn run_inner_uses_no_std_fast_path_for_core_source() {
        clear_std_cache();
        let output = run_inner("my id x = x\nid(42)\n");

        assert!(output.ok, "{output:?}");
        assert_eq!(output.file_count, 1);
        assert_eq!(
            output
                .timings
                .as_ref()
                .map(|timing| timing.used_embedded_std),
            Some(false)
        );
        assert_eq!(
            output.results.first().map(|result| result.value.as_str()),
            Some("42")
        );
        assert_eq!(output.text, "run roots [42]\n");
    }

    #[test]
    fn run_inner_retries_unresolved_core_names_with_embedded_std() {
        clear_std_cache();
        let output = run_inner("1 + 2\n");

        assert!(output.ok, "{output:?}");
        assert_eq!(
            output
                .timings
                .as_ref()
                .map(|timing| timing.used_embedded_std),
            Some(true)
        );
        assert_eq!(
            output.results.first().map(|result| result.value.as_str()),
            Some("3")
        );
    }

    #[test]
    fn run_inner_uses_compact_playground_std_for_mixed_numeric_add() {
        clear_std_cache();
        let output = run_inner("1 + 1.2\n");

        assert!(output.ok, "{output:?}");
        assert_eq!(
            output
                .timings
                .as_ref()
                .map(|timing| timing.used_embedded_std),
            Some(true)
        );
        assert_eq!(
            output.results.first().map(|result| result.value.as_str()),
            Some("2.2")
        );
        assert!(output.file_count < yulang::stdlib::embedded_std_files().len() + 1);
    }

    #[test]
    fn run_inner_uses_compact_playground_std_for_struct_method_example() {
        clear_std_cache();
        let output = run_inner(
            "\
struct point { x: int, y: int } with:
    our p.norm2 = p.x * p.x + p.y * p.y

point { x: 3, y: 4 } .norm2 + 1.12
",
        );

        assert!(output.ok, "{output:?}");
        assert_eq!(
            output
                .timings
                .as_ref()
                .map(|timing| timing.used_embedded_std),
            Some(true)
        );
        assert_eq!(
            output.results.first().map(|result| result.value.as_str()),
            Some("26.12")
        );
        assert!(output.file_count < yulang::stdlib::embedded_std_files().len() + 1);
    }

    #[test]
    fn run_inner_uses_compact_playground_std_for_list_update_example() {
        clear_std_cache();
        let output = run_inner(
            "\
{
    my $xs = [
        2
        3
        4
    ]
    &xs[1] = 6
    $xs
}
",
        );

        assert!(output.ok, "{output:?}");
        assert_eq!(
            output
                .timings
                .as_ref()
                .map(|timing| timing.used_embedded_std),
            Some(true)
        );
        assert_eq!(
            output.results.first().map(|result| result.value.as_str()),
            Some("[2, 6, 4]")
        );
        assert!(output.file_count < yulang::stdlib::embedded_std_files().len() + 1);
    }

    #[test]
    fn run_inner_uses_embedded_std_only_when_needed() {
        clear_std_cache();
        let output = run_inner("each(1..3).list\n");

        assert!(output.ok, "{output:?}");
        assert_eq!(
            output
                .timings
                .as_ref()
                .map(|timing| timing.used_embedded_std),
            Some(true)
        );
        assert_eq!(output.text, "run roots [[1, 2, 3]]\n");
    }

    #[test]
    fn run_inner_routes_junction_prelude_names_to_embedded_std() {
        clear_std_cache();
        let output = run_inner("if all [1, 2, 3] < any [2, 3, 4]:\n  1\nelse:\n  0\n");

        assert!(output.ok, "{output:?}");
        assert_eq!(
            output
                .timings
                .as_ref()
                .map(|timing| timing.used_embedded_std),
            Some(true)
        );
        assert_eq!(output.text, "run roots [1]\n");
    }

    #[test]
    fn run_inner_handles_console_out_as_stdout() {
        clear_std_cache();
        let output = run_inner("println \"hello\"\n1 + 2\n");

        assert!(output.ok, "{output:?}");
        assert_eq!(output.stdout, "hello\n");
        assert_eq!(
            output.results.first().map(|result| result.value.as_str()),
            Some("()")
        );
        assert_eq!(
            output.results.get(1).map(|result| result.value.as_str()),
            Some("3")
        );
    }

    #[test]
    fn colorize_inner_reports_token_spans() {
        let output = colorize_inner("// note\nmy x = \"日本語\"\n");

        assert!(output.ok, "{output:?}");
        assert!(output.spans.iter().any(|span| {
            span.kind == HighlightKind::Comment && span.start == 0 && span.end == 7
        }));
        assert!(output.spans.iter().any(|span| {
            span.kind == HighlightKind::Keyword && span.start == 8 && span.end == 10
        }));
        assert!(
            output
                .spans
                .iter()
                .any(|span| { span.kind == HighlightKind::String && span.start >= 15 })
        );
    }

    #[test]
    fn run_inner_caches_repeated_source() {
        clear_std_cache();
        let first = run_inner("my id x = x\nid(42)\n");
        let second = run_inner("my id x = x\nid(42)\n");

        assert!(first.ok, "{first:?}");
        assert!(second.ok, "{second:?}");
        assert_eq!(
            second
                .timings
                .as_ref()
                .map(|timing| timing.source_cache_hits),
            Some(1)
        );
    }

    #[test]
    fn check_inner_returns_structured_diagnostic() {
        let output = check_inner("my x: int = true\n");

        assert!(!output.ok, "{output:?}");
        assert_eq!(output.diagnostics.len(), 1);
        assert_eq!(output.diagnostics[0].label.as_deref(), Some("x"));
        assert_eq!(
            output.diagnostics[0].message,
            "type mismatch: bool is not int"
        );
    }

    #[test]
    fn dump_poly_inner_reports_lowering_errors() {
        let output = dump_poly_inner("my x: int = true\n");

        assert!(!output.ok, "{output:?}");
        assert!(output.text.contains("my d"));
        assert_eq!(output.errors, vec!["type mismatch: bool is not int"]);
    }
}
