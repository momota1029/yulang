use serde::Serialize;
use yulang_editor::{OpTable, semantic_tokens};
use yulang_infer::{DefId, LowerState, Path as InferPath};

use crate::output::Diagnostic;

#[derive(Debug, Clone, Serialize)]
pub struct ColorizeOutput {
    pub ok: bool,
    pub spans: Vec<HighlightSpan>,
    pub diagnostics: Vec<Diagnostic>,
}

#[derive(Debug, Clone, Serialize)]
pub struct HighlightSpan {
    pub start: usize,
    pub end: usize,
    pub kind: HighlightKind,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize)]
#[serde(rename_all = "kebab-case")]
pub enum HighlightKind {
    Function,
    Type,
    TypeParameter,
    Namespace,
    Parameter,
    Keyword,
    String,
    Number,
    Comment,
    Operator,
    Delimiter,
    Colon,
    Property,
    Pattern,
}

pub fn colorize_source_with_context(
    source: &str,
    op_table: Option<OpTable>,
    highlights: Option<&semantic_tokens::ResolvedHighlightInfo>,
) -> ColorizeOutput {
    let encoded =
        semantic_tokens::compute_with_op_table_and_highlights(source, op_table, highlights);
    ColorizeOutput {
        ok: true,
        spans: semantic_spans(source, &encoded),
        diagnostics: Vec::new(),
    }
}

pub fn resolved_highlights_from_lower_state(
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

fn semantic_spans(source: &str, encoded: &[u32]) -> Vec<HighlightSpan> {
    let line_starts = line_utf16_starts(source);
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
        let len = chunk[2] as usize;
        let Some(kind) = highlight_kind(chunk[3]) else {
            continue;
        };
        spans.push(HighlightSpan {
            start: line_start + col,
            end: line_start + col + len,
            kind,
        });
    }

    spans
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

fn highlight_kind(token_type: u32) -> Option<HighlightKind> {
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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn colorize_reports_lsp_token_kinds() {
        let output = colorize_source_with_context("// note\nmy answer = 1", None, None);

        assert!(output.spans.iter().any(|span| {
            span.kind == HighlightKind::Comment && span.start == 0 && span.end == 7
        }));
        assert!(output.spans.iter().any(|span| {
            span.kind == HighlightKind::Keyword && span.start == 8 && span.end == 10
        }));
        assert!(output.spans.iter().any(|span| {
            span.kind == HighlightKind::Delimiter && span.start == 18 && span.end == 19
        }));
    }

    #[test]
    fn colorize_reports_utf16_offsets() {
        let source = "my s = \"日本語\"\nmy x = 1\n";
        let my_byte_offset = source.rfind("my").expect("my keyword");
        let my_utf16_offset = source[..my_byte_offset].encode_utf16().count();

        let output = colorize_source_with_context(source, None, None);

        assert!(output.spans.iter().any(|span| {
            span.kind == HighlightKind::Keyword
                && span.start == my_utf16_offset
                && span.end == my_utf16_offset + "my".len()
        }));
    }
}
