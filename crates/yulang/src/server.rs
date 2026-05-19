use std::collections::{HashMap, HashSet};
use std::path::PathBuf;
use std::sync::Mutex;

use tower_lsp::jsonrpc::Result;
use tower_lsp::lsp_types::*;
use tower_lsp::{Client, LanguageServer, LspService, Server};
use yulang_editor::semantic_tokens;
use yulang_infer::simplify::compact::{
    CompactBounds, CompactFun, CompactType, CompactTypeScheme, compact_type_var,
    compact_type_vars_in_order,
};
use yulang_infer::{
    DefId, FileSpan, LowerState, Name as InferName, Path as InferPath, TypeVar,
    collect_compact_results_for_paths_in_scope, collect_surface_diagnostics, export_core_program,
    format_coalesced_scheme_in_scope, lower_virtual_source_with_options,
    surface_diagnostic::SurfaceDiagnostic,
};
use yulang_parser::lex::SyntaxKind;
use yulang_parser::sink::YulangLanguage;
use yulang_runtime as runtime;
use yulang_sources::{
    SourceOptions, collect_virtual_source_files_with_options, is_std_root,
    resolve_or_install_std_root,
};
use yulang_typed_ir as typed_ir;

type SyntaxNode = rowan::SyntaxNode<YulangLanguage>;
type SyntaxToken = rowan::SyntaxToken<YulangLanguage>;

struct Backend {
    client: Client,
    std_root: Option<PathBuf>,
    documents: Mutex<HashMap<Url, String>>,
}

impl Backend {
    fn source_options(&self, base_dir: Option<&std::path::Path>) -> SourceOptions {
        let std_root = resolve_or_install_std_root(self.std_root.clone(), base_dir)
            .ok()
            .flatten();
        SourceOptions {
            std_root,
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
        let uri_for_diagnostics = uri.clone();
        let diagnostics = tokio::task::spawn_blocking(move || {
            match lower_virtual_source_with_options(&source, base_dir, options) {
                Ok(lowered) => {
                    diagnostics_for_lowered_source(&uri_for_diagnostics, &source, lowered)
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
}

fn diagnostics_for_lowered_source(
    uri: &Url,
    document_source: &str,
    mut lowered: yulang_infer::LoweredSources,
) -> Vec<Diagnostic> {
    let surface = collect_surface_diagnostics(&lowered.state);
    let mut diagnostics = surface_to_lsp(uri, &lowered.diagnostic_source, document_source, surface);
    if !diagnostics.is_empty() {
        return diagnostics;
    }

    let program = export_core_program(&mut lowered.state);
    let evidence = program.evidence.clone();
    if let Err(error) = runtime::lower_core_program(program).and_then(runtime::monomorphize_module)
        && let Some(diagnostic) = runtime_error_to_lsp(
            uri,
            &lowered.diagnostic_source,
            document_source,
            &evidence,
            &error,
        )
    {
        diagnostics.push(diagnostic);
    }
    diagnostics
}

fn surface_to_lsp(
    uri: &Url,
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
            let related_information = d
                .related
                .into_iter()
                .filter_map(|related| {
                    let range = related
                        .span
                        .and_then(|span| shift_span_to_document(span, prefix_len))
                        .map(|span| byte_range_to_lsp(&line_starts, span))?;
                    Some(DiagnosticRelatedInformation {
                        location: Location {
                            uri: uri.clone(),
                            range,
                        },
                        message: related.message,
                    })
                })
                .collect::<Vec<_>>();
            Diagnostic {
                range,
                severity: Some(DiagnosticSeverity::ERROR),
                message: d.message,
                related_information: (!related_information.is_empty())
                    .then_some(related_information),
                ..Default::default()
            }
        })
        .collect()
}

fn runtime_error_to_lsp(
    uri: &Url,
    diagnostic_source: &str,
    document_source: &str,
    evidence: &typed_ir::PrincipalEvidence,
    error: &runtime::RuntimeError,
) -> Option<Diagnostic> {
    let runtime::RuntimeError::TypeMismatch {
        expected,
        actual,
        context: Some(context),
        ..
    } = error
    else {
        return None;
    };
    let prefix_len = diagnostic_prefix_len(diagnostic_source, document_source);
    let line_starts = line_starts(document_source);
    let primary_edge = runtime_type_mismatch_primary_edge(context, evidence);
    let primary_range = primary_edge
        .and_then(|edge| edge.source_range)
        .and_then(|range| source_range_to_lsp(&line_starts, range, prefix_len))
        .unwrap_or_default();
    let mut related = Vec::new();
    let actual_edge = runtime_type_mismatch_actual_edge(context, evidence);
    push_runtime_type_related(
        &mut related,
        uri,
        &line_starts,
        prefix_len,
        actual_edge,
        runtime_type_related_message("actual", actual, actual_edge),
    );
    let expected_edge = runtime_type_mismatch_expected_edge(context, evidence);
    push_runtime_type_related(
        &mut related,
        uri,
        &line_starts,
        prefix_len,
        expected_edge,
        runtime_type_related_message("expected", expected, expected_edge),
    );

    Some(Diagnostic {
        range: primary_range,
        severity: Some(DiagnosticSeverity::ERROR),
        code: Some(NumberOrString::String("type-mismatch".to_string())),
        source: Some("yulang".to_string()),
        message: error.to_string(),
        related_information: (!related.is_empty()).then_some(related),
        ..Default::default()
    })
}

fn runtime_type_mismatch_primary_edge<'a>(
    context: &runtime::diagnostic::TypeMismatchContext,
    evidence: &'a typed_ir::PrincipalEvidence,
) -> Option<&'a typed_ir::ExpectedEdgeEvidence> {
    match context.phase {
        runtime::diagnostic::TypeMismatchPhase::ApplyCallee => context.callee_source_edge,
        runtime::diagnostic::TypeMismatchPhase::ApplyArgument => context.arg_source_edge,
        runtime::diagnostic::TypeMismatchPhase::ApplyResult
        | runtime::diagnostic::TypeMismatchPhase::Expected => {
            context.arg_source_edge.or(context.callee_source_edge)
        }
    }
    .and_then(|id| evidence.expected_edge(id))
}

fn runtime_type_mismatch_actual_edge<'a>(
    context: &runtime::diagnostic::TypeMismatchContext,
    evidence: &'a typed_ir::PrincipalEvidence,
) -> Option<&'a typed_ir::ExpectedEdgeEvidence> {
    match context.phase {
        runtime::diagnostic::TypeMismatchPhase::ApplyCallee => context.callee_source_edge,
        runtime::diagnostic::TypeMismatchPhase::ApplyArgument => context.arg_source_edge,
        runtime::diagnostic::TypeMismatchPhase::ApplyResult
        | runtime::diagnostic::TypeMismatchPhase::Expected => {
            context.arg_source_edge.or(context.callee_source_edge)
        }
    }
    .and_then(|id| evidence.expected_edge(id))
}

fn runtime_type_mismatch_expected_edge<'a>(
    context: &runtime::diagnostic::TypeMismatchContext,
    evidence: &'a typed_ir::PrincipalEvidence,
) -> Option<&'a typed_ir::ExpectedEdgeEvidence> {
    match context.phase {
        runtime::diagnostic::TypeMismatchPhase::ApplyCallee => context.arg_source_edge,
        runtime::diagnostic::TypeMismatchPhase::ApplyArgument => context.callee_source_edge,
        runtime::diagnostic::TypeMismatchPhase::ApplyResult
        | runtime::diagnostic::TypeMismatchPhase::Expected => {
            context.callee_source_edge.or(context.arg_source_edge)
        }
    }
    .and_then(|id| evidence.expected_edge(id))
}

fn runtime_type_related_message(
    role: &str,
    ty: &typed_ir::Type,
    edge: Option<&typed_ir::ExpectedEdgeEvidence>,
) -> String {
    let mut message = format!(
        "{role} type here is `{}`",
        runtime::diagnostic::display_type(ty)
    );
    if let Some(edge) = edge {
        message.push_str(" (");
        message.push_str(expected_edge_kind_label(edge.kind));
        message.push(')');
    }
    message
}

fn expected_edge_kind_label(kind: typed_ir::ExpectedEdgeKind) -> &'static str {
    match kind {
        typed_ir::ExpectedEdgeKind::IfCondition => "if condition",
        typed_ir::ExpectedEdgeKind::IfBranch => "if branch",
        typed_ir::ExpectedEdgeKind::MatchGuard => "match guard",
        typed_ir::ExpectedEdgeKind::MatchBranch => "match branch",
        typed_ir::ExpectedEdgeKind::CatchGuard => "catch guard",
        typed_ir::ExpectedEdgeKind::CatchBranch => "catch branch",
        typed_ir::ExpectedEdgeKind::ApplicationCallee => "application callee",
        typed_ir::ExpectedEdgeKind::ApplicationArgument => "application argument",
        typed_ir::ExpectedEdgeKind::Annotation => "annotation",
        typed_ir::ExpectedEdgeKind::RecordField => "record field",
        typed_ir::ExpectedEdgeKind::VariantPayload => "variant payload",
        typed_ir::ExpectedEdgeKind::AssignmentValue => "assignment value",
        typed_ir::ExpectedEdgeKind::RepresentationCoerce => "representation coercion",
    }
}

fn push_runtime_type_related(
    related: &mut Vec<DiagnosticRelatedInformation>,
    uri: &Url,
    line_starts: &[usize],
    prefix_len: usize,
    edge: Option<&typed_ir::ExpectedEdgeEvidence>,
    message: String,
) {
    let Some(range) = edge
        .and_then(|edge| edge.source_range)
        .and_then(|range| source_range_to_lsp(line_starts, range, prefix_len))
    else {
        return;
    };
    related.push(DiagnosticRelatedInformation {
        location: Location {
            uri: uri.clone(),
            range,
        },
        message,
    });
}

fn diagnostic_prefix_len(diagnostic_source: &str, document_source: &str) -> usize {
    diagnostic_source
        .strip_suffix(document_source)
        .map(str::len)
        .unwrap_or(0)
}

fn source_range_to_lsp(
    line_starts: &[usize],
    range: typed_ir::SourceRange,
    prefix_len: usize,
) -> Option<Range> {
    let start = usize::try_from(range.start).ok()?.checked_sub(prefix_len)?;
    let end = usize::try_from(range.end).ok()?.checked_sub(prefix_len)?;
    Some(byte_range_to_lsp(
        line_starts,
        rowan::TextRange::new((start as u32).into(), (end as u32).into()),
    ))
}

fn shift_span_to_document(span: rowan::TextRange, prefix_len: usize) -> Option<rowan::TextRange> {
    let start = usize::from(span.start()).checked_sub(prefix_len)?;
    let end = usize::from(span.end()).checked_sub(prefix_len)?;
    Some(rowan::TextRange::new(
        (start as u32).into(),
        (end as u32).into(),
    ))
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

fn position_to_byte(line_starts: &[usize], position: Position) -> Option<usize> {
    let line = usize::try_from(position.line).ok()?;
    let line_start = *line_starts.get(line)?;
    Some(line_start + usize::try_from(position.character).ok()?)
}

fn byte_range_to_lsp(line_starts: &[usize], span: rowan::TextRange) -> Range {
    Range {
        start: byte_to_position(line_starts, usize::from(span.start())),
        end: byte_to_position(line_starts, usize::from(span.end())),
    }
}

fn range_contains_position(range: Range, position: Position) -> bool {
    (range.start.line, range.start.character) <= (position.line, position.character)
        && (position.line, position.character) <= (range.end.line, range.end.character)
}

fn document_symbols(source: &str) -> Vec<DocumentSymbol> {
    let green = yulang_parser::parse_module_to_green(source);
    let root = SyntaxNode::new_root(green);
    let line_starts = line_starts(source);
    root.children()
        .filter_map(|node| document_symbol_for_node(&node, &line_starts))
        .collect()
}

#[derive(Clone)]
struct HoverTarget {
    name: String,
    path: Vec<String>,
    path_index: usize,
    range: Range,
    token_kind: SyntaxKind,
    in_type_expr: bool,
    syntax_range: rowan::TextRange,
}

fn hover_target_at(source: &str, position: Position) -> Option<HoverTarget> {
    let line_starts = line_starts(source);
    let _offset = position_to_byte(&line_starts, position)?;
    let green = yulang_parser::parse_module_to_green(source);
    let root = SyntaxNode::new_root(green);

    let tokens = root
        .descendants_with_tokens()
        .filter_map(|it| it.into_token())
        .filter(|token| is_hover_name_token(token) || token.kind() == SyntaxKind::ColonColon)
        .map(|token| {
            let syntax_range = token.text_range();
            let range = byte_range_to_lsp(&line_starts, syntax_range);
            (token, range, syntax_range)
        })
        .collect::<Vec<_>>();

    let target_idx = tokens.iter().position(|(token, range, _)| {
        is_hover_name_token(token) && range_contains_position(*range, position)
    })?;
    let (start_idx, end_idx) = hover_path_bounds(&tokens, target_idx);
    let path_tokens = (start_idx..=end_idx)
        .step_by(2)
        .filter_map(|idx| tokens.get(idx))
        .filter(|(token, _, _)| is_hover_name_token(token))
        .collect::<Vec<_>>();
    let path = path_tokens
        .iter()
        .map(|(token, _, _)| hover_name_text(token))
        .collect::<Vec<_>>();
    let path_index = path_tokens
        .iter()
        .position(|(token, _, _)| token == &tokens[target_idx].0)?;
    let name = path.get(path_index)?.clone();
    Some(HoverTarget {
        name,
        path,
        path_index,
        range: tokens[target_idx].1,
        token_kind: tokens[target_idx].0.kind(),
        in_type_expr: token_has_ancestor(&tokens[target_idx].0, SyntaxKind::TypeExpr),
        syntax_range: tokens[target_idx].2,
    })
}

fn is_hover_name_token(token: &SyntaxToken) -> bool {
    matches!(
        token.kind(),
        SyntaxKind::Ident
            | SyntaxKind::SigilIdent
            | SyntaxKind::OpName
            | SyntaxKind::DotField
            | SyntaxKind::Infix
            | SyntaxKind::Prefix
            | SyntaxKind::Suffix
            | SyntaxKind::Nullfix
    )
}

fn hover_name_text(token: &SyntaxToken) -> String {
    token.text().trim_start_matches('.').to_string()
}

fn token_has_ancestor(token: &SyntaxToken, kind: SyntaxKind) -> bool {
    token.parent_ancestors().any(|node| node.kind() == kind)
}

fn hover_path_bounds(
    tokens: &[(SyntaxToken, Range, rowan::TextRange)],
    target_idx: usize,
) -> (usize, usize) {
    let mut start_idx = target_idx;
    while start_idx >= 2
        && tokens[start_idx - 1].0.kind() == SyntaxKind::ColonColon
        && is_hover_name_token(&tokens[start_idx - 2].0)
    {
        start_idx -= 2;
    }

    let mut end_idx = target_idx;
    while end_idx + 2 < tokens.len()
        && tokens[end_idx + 1].0.kind() == SyntaxKind::ColonColon
        && is_hover_name_token(&tokens[end_idx + 2].0)
    {
        end_idx += 2;
    }

    (start_idx, end_idx)
}

fn hover_type_from_lower_state(
    state: &mut LowerState,
    target: &HoverTarget,
) -> Option<(String, String)> {
    if target.in_type_expr {
        return None;
    }

    if let Some((recv_tv, recv_eff, result_tv, result_eff)) =
        resolve_hover_target_selection_tvs(state, target)
    {
        return hover_type_for_selection(
            state,
            &target.name,
            recv_tv,
            recv_eff,
            result_tv,
            result_eff,
        );
    }

    if let Some(def) = resolve_hover_target_source_def(state, target) {
        return hover_type_for_def(state, def);
    }

    if let Some(def) = resolve_hover_target_def(state, target) {
        return hover_type_for_def(state, def);
    }

    None
}

fn resolve_hover_target_selection_tvs(
    state: &LowerState,
    target: &HoverTarget,
) -> Option<(TypeVar, TypeVar, TypeVar, TypeVar)> {
    let entry = state.entry_file_id()?;
    state.selection_spans.iter().rev().find_map(|span| {
        (span.span.file == entry && span_contains_range(span.span.range, target.syntax_range))
            .then_some((
                span.recv_tv,
                span.recv_eff,
                span.result_tv,
                span.result_eff,
            ))
    })
}

fn resolve_hover_target_source_def(state: &LowerState, target: &HoverTarget) -> Option<DefId> {
    let entry = state.entry_file_id()?;
    state
        .value_use_spans
        .iter()
        .rev()
        .find_map(|(span, def)| {
            (span.file == entry && span_contains_range(span.range, target.syntax_range))
                .then_some(*def)
        })
        .or_else(|| {
            state.ref_spans.iter().find_map(|(ref_id, span)| {
                (span.file == entry && span_contains_range(span.range, target.syntax_range))
                    .then(|| state.ctx.refs.get(*ref_id))
                    .flatten()
            })
        })
        .or_else(|| narrowest_def_span_containing(state, target.syntax_range))
}

fn span_contains_range(outer: rowan::TextRange, inner: rowan::TextRange) -> bool {
    outer.start() <= inner.start() && inner.end() <= outer.end()
}

fn narrowest_def_span_containing(state: &LowerState, target: rowan::TextRange) -> Option<DefId> {
    let entry = state.entry_file_id()?;
    state
        .def_spans
        .iter()
        .filter(|(_, span)| span.file == entry && span_contains_range(span.range, target))
        .min_by_key(|(_, span)| usize::from(span.range.end()) - usize::from(span.range.start()))
        .map(|(def, _)| *def)
}

fn resolve_hover_target_def(state: &LowerState, target: &HoverTarget) -> Option<DefId> {
    let is_path_tail = target.path_index + 1 == target.path.len();
    if target.path.len() > 1 && is_path_tail {
        return state.ctx.resolve_path_value(&infer_path(&target.path));
    }
    if target.path.len() == 1 && target.token_kind == SyntaxKind::OpName {
        return state
            .ctx
            .resolve_value(&InferName(target.name.clone()))
            .or_else(|| resolve_unique_named_def(state, &target.name));
    }
    None
}

fn hover_type_for_def(state: &mut LowerState, def: DefId) -> Option<(String, String)> {
    if let (Some(name), Some(ty)) = (state.def_name(def), state.def_hover_types.get(&def)) {
        return Some((name.0.clone(), ty.clone()));
    }
    state.finalize_compact_results();
    let paths = hover_paths_for_def(state, def);
    if let Some(result) = collect_compact_results_for_paths_in_scope(state, &paths, &state.ctx)
        .into_iter()
        .next()
    {
        return Some(result);
    }
    let name = state.def_name(def)?.0.clone();
    let scheme = compact_hover_scheme(state, def)?;
    Some((name, format_coalesced_scheme_in_scope(&scheme, &state.ctx)))
}

fn hover_type_for_selection(
    state: &mut LowerState,
    name: &str,
    recv_tv: TypeVar,
    recv_eff: TypeVar,
    result_tv: TypeVar,
    result_eff: TypeVar,
) -> Option<(String, String)> {
    if let Some(def) = state.resolved_selection_def(result_tv) {
        if let Some(public_def) = public_effect_method_hover_def(state, def) {
            if let Some((_, ty)) = hover_type_for_def(state, public_def) {
                return Some((name.to_string(), ty));
            }
        }
        if let Some((_, ty)) = hover_type_for_def(state, def) {
            return Some((name.to_string(), ty));
        }
    }

    state.finalize_compact_results();
    let direct = compact_hover_selection_scheme(state, recv_tv, recv_eff, result_tv, result_eff);
    let scheme = if compact_scheme_has_union_surface(&direct) {
        let mut source_defs = state.def_spans.keys().copied().collect::<Vec<_>>();
        source_defs.sort_by_key(|def| def.0);
        let mut roots = source_defs
            .into_iter()
            .filter_map(|def| state.def_tvs.get(&def).copied())
            .collect::<Vec<_>>();
        push_selection_hover_roots(&mut roots, recv_tv, recv_eff, result_tv, result_eff);
        compact_hover_selection_scheme_from_roots(
            state, recv_tv, recv_eff, result_tv, result_eff, &roots,
        )
        .unwrap_or(direct)
    } else {
        direct
    };
    Some((
        name.to_string(),
        format_coalesced_scheme_in_scope(&scheme, &state.ctx),
    ))
}

fn public_effect_method_hover_def(state: &LowerState, def: DefId) -> Option<DefId> {
    let info = state
        .infer
        .effect_methods
        .values()
        .flat_map(|infos| infos.iter())
        .find(|info| info.def == def)?;
    let mut path = info.effect.clone();
    path.segments.push(info.name.clone());
    state.ctx.resolve_path_value(&path)
}

fn compact_hover_selection_scheme(
    state: &LowerState,
    recv_tv: TypeVar,
    recv_eff: TypeVar,
    result_tv: TypeVar,
    result_eff: TypeVar,
) -> CompactTypeScheme {
    let mut roots = Vec::new();
    push_selection_hover_roots(&mut roots, recv_tv, recv_eff, result_tv, result_eff);
    compact_hover_selection_scheme_from_roots(
        state, recv_tv, recv_eff, result_tv, result_eff, &roots,
    )
    .unwrap_or_else(|| compact_type_var(&state.infer, result_tv))
}

fn compact_hover_selection_scheme_from_roots(
    state: &LowerState,
    recv_tv: TypeVar,
    recv_eff: TypeVar,
    result_tv: TypeVar,
    result_eff: TypeVar,
    roots: &[TypeVar],
) -> Option<CompactTypeScheme> {
    let compacted = compact_type_vars_in_order(&state.infer, roots);
    let selection_start = roots.len().checked_sub(4)?;
    debug_assert_eq!(roots[selection_start], recv_tv);
    debug_assert_eq!(roots[selection_start + 1], recv_eff);
    debug_assert_eq!(roots[selection_start + 2], result_eff);
    debug_assert_eq!(roots[selection_start + 3], result_tv);
    let recv = compacted.get(selection_start)?;
    let recv_eff = compacted.get(selection_start + 1)?;
    let result_eff = compacted.get(selection_start + 2)?;
    let result = compacted.get(selection_start + 3)?;
    let lower_fun = CompactFun {
        arg: recv.cty.lower.clone(),
        arg_eff: recv_eff.cty.lower.clone(),
        ret_eff: result_eff.cty.lower.clone(),
        ret: result.cty.lower.clone(),
    };
    let upper_fun = CompactFun {
        arg: recv.cty.upper.clone(),
        arg_eff: recv_eff.cty.upper.clone(),
        ret_eff: result_eff.cty.upper.clone(),
        ret: result.cty.upper.clone(),
    };
    Some(CompactTypeScheme {
        cty: CompactBounds {
            self_var: None,
            lower: CompactType {
                funs: vec![lower_fun],
                ..CompactType::default()
            },
            upper: CompactType {
                funs: vec![upper_fun],
                ..CompactType::default()
            },
        },
        rec_vars: merge_compact_rec_vars(&compacted),
    })
}

fn push_selection_hover_roots(
    roots: &mut Vec<TypeVar>,
    recv_tv: TypeVar,
    recv_eff: TypeVar,
    result_tv: TypeVar,
    result_eff: TypeVar,
) {
    roots.extend([recv_tv, recv_eff, result_eff, result_tv]);
}

fn merge_compact_rec_vars(
    schemes: &[CompactTypeScheme],
) -> std::collections::HashMap<TypeVar, CompactBounds> {
    schemes
        .iter()
        .flat_map(|scheme| {
            scheme
                .rec_vars
                .iter()
                .map(|(var, bounds)| (*var, bounds.clone()))
        })
        .collect()
}

fn compact_hover_scheme(
    state: &mut LowerState,
    def: DefId,
) -> Option<yulang_infer::simplify::compact::CompactTypeScheme> {
    if let Some(scheme) = state.compact_scheme_of(def) {
        return Some(scheme);
    }
    let def_tv = *state.def_tvs.get(&def)?;
    let direct = compact_type_var(&state.infer, def_tv);
    let Some(owner) = state.def_owner(def) else {
        return Some(direct);
    };
    if !compact_scheme_has_union_surface(&direct) {
        return Some(direct);
    }
    if let Some(owner_tv) = state.def_tvs.get(&owner).copied() {
        let target_defs = HashSet::from([owner, def]);
        state.finalize_compact_results_for_defs(&target_defs);
        if let Some(scheme) = state.compact_scheme_of(def) {
            return Some(scheme);
        }
        return compact_type_vars_in_order(&state.infer, &[owner_tv, def_tv])
            .into_iter()
            .last();
    }
    Some(direct)
}

fn compact_scheme_has_union_surface(
    scheme: &yulang_infer::simplify::compact::CompactTypeScheme,
) -> bool {
    compact_type_has_multiple_alternatives(&scheme.cty.lower)
        || compact_type_has_multiple_alternatives(&scheme.cty.upper)
}

fn compact_type_has_multiple_alternatives(
    ty: &yulang_infer::simplify::compact::CompactType,
) -> bool {
    let mut alternatives = ty.vars.len()
        + ty.prims.len()
        + ty.cons.len()
        + ty.funs.len()
        + ty.records.len()
        + ty.record_spreads.len()
        + ty.variants.len()
        + ty.tuples.len()
        + ty.rows.len();
    alternatives += ty
        .funs
        .iter()
        .filter(|fun| {
            compact_type_has_multiple_alternatives(&fun.arg)
                || compact_type_has_multiple_alternatives(&fun.ret)
        })
        .count();
    alternatives > 1
}

fn hover_paths_for_def(state: &LowerState, def: DefId) -> Vec<(InferPath, DefId)> {
    let mut paths = state
        .ctx
        .collect_all_binding_paths()
        .into_iter()
        .filter(|(_, current)| *current == def)
        .collect::<Vec<_>>();
    if paths.is_empty() {
        if let Some(name) = state.def_name(def) {
            paths.push((
                InferPath {
                    segments: vec![name.clone()],
                },
                def,
            ));
        }
    }
    paths
}

fn resolve_unique_named_def(state: &LowerState, name: &str) -> Option<DefId> {
    let mut matches = state
        .def_names
        .iter()
        .filter_map(|(&def, def_name)| (def_name.0 == name).then_some(def));
    let first = matches.next()?;
    matches.next().is_none().then_some(first)
}

fn infer_path(segments: &[String]) -> InferPath {
    InferPath {
        segments: segments
            .iter()
            .map(|segment| InferName(segment.clone()))
            .collect(),
    }
}

fn hover_label(name: &str, rendered_name: &str) -> String {
    if rendered_name.ends_with(name) {
        rendered_name.to_string()
    } else {
        name.to_string()
    }
}

fn hover_for_source(
    source: &str,
    base_dir: Option<PathBuf>,
    options: SourceOptions,
    position: Position,
) -> Option<Hover> {
    let target = hover_target_at(source, position)?;
    let mut lowered = lower_virtual_source_with_options(source, base_dir, options).ok()?;
    let (rendered_name, ty) = hover_type_from_lower_state(&mut lowered.state, &target)?;
    let label = hover_label(&target.name, &rendered_name);
    Some(Hover {
        contents: HoverContents::Markup(MarkupContent {
            kind: MarkupKind::Markdown,
            value: format!("```yulang\n{label}: {ty}\n```"),
        }),
        range: Some(target.range),
    })
}

fn goto_definition_for_source(
    uri: Url,
    source: &str,
    base_dir: Option<PathBuf>,
    options: SourceOptions,
    position: Position,
) -> Option<Location> {
    let target = hover_target_at(source, position)?;
    let mut lowered = lower_virtual_source_with_options(source, base_dir, options).ok()?;
    let def = resolve_target_def_id(&mut lowered.state, &target)?;
    let file_span = lowered.state.def_spans.get(&def).copied()?;
    locate_file_span(&lowered.state, file_span, &uri, source)
}

fn locate_file_span(
    state: &LowerState,
    file_span: FileSpan,
    entry_uri: &Url,
    entry_source: &str,
) -> Option<Location> {
    let entry_file_id = state.entry_file_id();
    if Some(file_span.file) == entry_file_id {
        let line_starts = line_starts(entry_source);
        return Some(Location {
            uri: entry_uri.clone(),
            range: byte_range_to_lsp(&line_starts, file_span.range),
        });
    }

    let info = state.file_info(file_span.file)?;
    let target_uri = Url::from_file_path(&info.path).ok()?;
    let target_source = std::fs::read_to_string(&info.path).ok()?;
    let line_starts = line_starts(&target_source);
    Some(Location {
        uri: target_uri,
        range: byte_range_to_lsp(&line_starts, file_span.range),
    })
}

fn rename_for_source(
    entry_uri: Url,
    entry_source: &str,
    base_dir: Option<PathBuf>,
    options: SourceOptions,
    position: Position,
    new_name: &str,
) -> Option<WorkspaceEdit> {
    if !is_valid_rename_identifier(new_name) {
        return None;
    }
    let target = hover_target_at(entry_source, position)?;
    let mut lowered =
        lower_virtual_source_with_options(entry_source, base_dir, options).ok()?;
    let def = resolve_target_def_id(&mut lowered.state, &target)?;

    // operator は v1 では rename しない（fixity 区分が表示用ラベルから外れているため）。
    if lowered.state.ctx.operator_fixity(def).is_some() {
        return None;
    }

    let def_span = lowered.state.def_spans.get(&def).copied()?;
    if !is_user_writable_file(&lowered.state, def_span.file) {
        return None;
    }

    let mut spans: Vec<FileSpan> = Vec::new();
    spans.push(def_span);
    for (span, candidate) in &lowered.state.value_use_spans {
        if *candidate == def && is_user_writable_file(&lowered.state, span.file) {
            spans.push(*span);
        }
    }
    spans.sort_by_key(|span| (span.file.0, span.range.start()));
    spans.dedup();

    let mut changes: HashMap<Url, Vec<TextEdit>> = HashMap::new();
    let mut file_sources: HashMap<yulang_infer::FileId, (Url, Vec<usize>)> = HashMap::new();
    let entry_file_id = lowered.state.entry_file_id();

    for span in spans {
        let (uri, line_starts_cached) = match file_sources.get(&span.file) {
            Some(cached) => cached.clone(),
            None => {
                let (uri, source) = if Some(span.file) == entry_file_id {
                    (entry_uri.clone(), entry_source.to_string())
                } else {
                    let info = lowered.state.file_info(span.file)?;
                    let uri = Url::from_file_path(&info.path).ok()?;
                    let source = std::fs::read_to_string(&info.path).ok()?;
                    (uri, source)
                };
                let line_starts_owned = line_starts(&source);
                let entry = (uri, line_starts_owned);
                file_sources.insert(span.file, entry.clone());
                entry
            }
        };
        let range = byte_range_to_lsp(&line_starts_cached, span.range);
        changes
            .entry(uri)
            .or_default()
            .push(TextEdit {
                range,
                new_text: new_name.to_string(),
            });
    }

    if changes.is_empty() {
        return None;
    }

    Some(WorkspaceEdit {
        changes: Some(changes),
        document_changes: None,
        change_annotations: None,
    })
}

fn is_user_writable_file(state: &LowerState, file: yulang_infer::FileId) -> bool {
    state
        .file_info(file)
        .map(|info| !matches!(info.origin, yulang_sources::SourceOrigin::Std))
        .unwrap_or(false)
}

fn is_valid_rename_identifier(name: &str) -> bool {
    let mut chars = name.chars();
    let Some(first) = chars.next() else {
        return false;
    };
    if !(first.is_ascii_alphabetic() || first == '_') {
        return false;
    }
    chars.all(|c| c.is_ascii_alphanumeric() || c == '_')
}

fn resolve_target_def_id(state: &mut LowerState, target: &HoverTarget) -> Option<DefId> {
    if let Some((_, _, result_tv, _)) = resolve_hover_target_selection_tvs(state, target) {
        if let Some(def) = state.resolved_selection_def(result_tv) {
            return Some(def);
        }
    }
    if let Some(def) = resolve_hover_target_source_def(state, target) {
        return Some(def);
    }
    resolve_hover_target_def(state, target)
}

fn document_symbol_for_node(node: &SyntaxNode, line_starts: &[usize]) -> Option<DocumentSymbol> {
    let spec = symbol_spec(node)?;
    let name_token = symbol_name_token(node, spec.name_kind);
    let name = name_token
        .as_ref()
        .map(|token| token.text().to_string())
        .or_else(|| spec.fallback_name)?;
    let range = byte_range_to_lsp(line_starts, node.text_range());
    let selection_range = name_token
        .map(|token| byte_range_to_lsp(line_starts, token.text_range()))
        .unwrap_or(range);
    #[allow(deprecated)]
    let symbol = DocumentSymbol {
        name,
        detail: spec.detail,
        kind: spec.kind,
        tags: None,
        deprecated: None,
        range,
        selection_range,
        children: None,
    };
    Some(symbol)
}

struct SymbolSpec {
    kind: SymbolKind,
    name_kind: SymbolNameKind,
    fallback_name: Option<String>,
    detail: Option<String>,
}

#[derive(Clone, Copy)]
enum SymbolNameKind {
    Ident,
    IdentOrOperator,
    TypeExprText,
}

fn symbol_spec(node: &SyntaxNode) -> Option<SymbolSpec> {
    let spec = match node.kind() {
        SyntaxKind::Binding => SymbolSpec {
            kind: SymbolKind::FUNCTION,
            name_kind: SymbolNameKind::IdentOrOperator,
            fallback_name: None,
            detail: None,
        },
        SyntaxKind::OpDef => SymbolSpec {
            kind: SymbolKind::OPERATOR,
            name_kind: SymbolNameKind::IdentOrOperator,
            fallback_name: None,
            detail: None,
        },
        SyntaxKind::StructDecl => SymbolSpec {
            kind: SymbolKind::STRUCT,
            name_kind: SymbolNameKind::Ident,
            fallback_name: None,
            detail: None,
        },
        SyntaxKind::EnumDecl | SyntaxKind::ErrorDecl => SymbolSpec {
            kind: SymbolKind::ENUM,
            name_kind: SymbolNameKind::Ident,
            fallback_name: None,
            detail: None,
        },
        SyntaxKind::ActDecl | SyntaxKind::RoleDecl => SymbolSpec {
            kind: SymbolKind::INTERFACE,
            name_kind: SymbolNameKind::Ident,
            fallback_name: None,
            detail: None,
        },
        SyntaxKind::TypeDecl => SymbolSpec {
            kind: SymbolKind::TYPE_PARAMETER,
            name_kind: SymbolNameKind::Ident,
            fallback_name: None,
            detail: None,
        },
        SyntaxKind::ImplDecl => SymbolSpec {
            kind: SymbolKind::OBJECT,
            name_kind: SymbolNameKind::TypeExprText,
            fallback_name: Some("impl".to_string()),
            detail: None,
        },
        SyntaxKind::ModDecl => SymbolSpec {
            kind: SymbolKind::MODULE,
            name_kind: SymbolNameKind::Ident,
            fallback_name: None,
            detail: None,
        },
        _ => return None,
    };
    Some(spec)
}

fn symbol_name_token(node: &SyntaxNode, kind: SymbolNameKind) -> Option<SyntaxToken> {
    match kind {
        SymbolNameKind::Ident => first_descendant_token(node, SyntaxKind::Ident),
        SymbolNameKind::IdentOrOperator => symbol_binding_name_token(node),
        SymbolNameKind::TypeExprText => first_type_expr_token(node),
    }
}

fn symbol_binding_name_token(node: &SyntaxNode) -> Option<SyntaxToken> {
    let header = child_node(node, SyntaxKind::BindingHeader)
        .or_else(|| child_node(node, SyntaxKind::OpDefHeader))?;
    let pattern = child_node(&header, SyntaxKind::Pattern).unwrap_or_else(|| header.clone());
    first_direct_token(&pattern, SyntaxKind::Ident)
        .or_else(|| first_direct_token(&pattern, SyntaxKind::OpName))
        .or_else(|| first_direct_token(&header, SyntaxKind::OpName))
}

fn first_type_expr_token(node: &SyntaxNode) -> Option<SyntaxToken> {
    let type_expr = child_node(node, SyntaxKind::TypeExpr)?;
    type_expr
        .descendants_with_tokens()
        .filter_map(|it| it.into_token())
        .find(|token| matches!(token.kind(), SyntaxKind::Ident | SyntaxKind::SigilIdent))
}

fn child_node(node: &SyntaxNode, kind: SyntaxKind) -> Option<SyntaxNode> {
    node.children().find(|child| child.kind() == kind)
}

fn first_direct_token(node: &SyntaxNode, kind: SyntaxKind) -> Option<SyntaxToken> {
    node.children_with_tokens()
        .filter_map(|it| it.into_token())
        .find(|token| token.kind() == kind)
}

fn first_descendant_token(node: &SyntaxNode, kind: SyntaxKind) -> Option<SyntaxToken> {
    node.descendants_with_tokens()
        .filter_map(|it| it.into_token())
        .find(|token| token.kind() == kind)
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
                hover_provider: Some(HoverProviderCapability::Simple(true)),
                definition_provider: Some(OneOf::Left(true)),
                rename_provider: Some(OneOf::Left(true)),
                document_symbol_provider: Some(OneOf::Left(true)),
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

    async fn document_symbol(
        &self,
        params: DocumentSymbolParams,
    ) -> Result<Option<DocumentSymbolResponse>> {
        let uri = params.text_document.uri;
        let source = self
            .documents
            .lock()
            .unwrap()
            .get(&uri)
            .cloned()
            .or_else(|| {
                uri.to_file_path()
                    .ok()
                    .and_then(|path| std::fs::read_to_string(path).ok())
            });
        let Some(source) = source else {
            return Ok(Some(DocumentSymbolResponse::Nested(Vec::new())));
        };
        let symbols = tokio::task::spawn_blocking(move || document_symbols(&source))
            .await
            .unwrap_or_default();
        Ok(Some(DocumentSymbolResponse::Nested(symbols)))
    }

    async fn hover(&self, params: HoverParams) -> Result<Option<Hover>> {
        let uri = params.text_document_position_params.text_document.uri;
        let position = params.text_document_position_params.position;
        let source = self
            .documents
            .lock()
            .unwrap()
            .get(&uri)
            .cloned()
            .or_else(|| {
                uri.to_file_path()
                    .ok()
                    .and_then(|path| std::fs::read_to_string(path).ok())
            });
        let Some(source) = source else {
            return Ok(None);
        };
        let base_dir = uri.to_file_path().ok().and_then(|path| {
            if path.is_dir() {
                Some(path)
            } else {
                path.parent().map(|parent| parent.to_path_buf())
            }
        });
        let options = self.source_options(base_dir.as_deref());
        let hover = tokio::task::spawn_blocking(move || {
            hover_for_source(&source, base_dir, options, position)
        })
        .await
        .unwrap_or_default();
        Ok(hover)
    }

    async fn goto_definition(
        &self,
        params: GotoDefinitionParams,
    ) -> Result<Option<GotoDefinitionResponse>> {
        let uri = params.text_document_position_params.text_document.uri;
        let position = params.text_document_position_params.position;
        let source = self
            .documents
            .lock()
            .unwrap()
            .get(&uri)
            .cloned()
            .or_else(|| {
                uri.to_file_path()
                    .ok()
                    .and_then(|path| std::fs::read_to_string(path).ok())
            });
        let Some(source) = source else {
            return Ok(None);
        };
        let base_dir = uri.to_file_path().ok().and_then(|path| {
            if path.is_dir() {
                Some(path)
            } else {
                path.parent().map(|parent| parent.to_path_buf())
            }
        });
        let options = self.source_options(base_dir.as_deref());
        let uri_for_task = uri.clone();
        let location = tokio::task::spawn_blocking(move || {
            goto_definition_for_source(uri_for_task, &source, base_dir, options, position)
        })
        .await
        .unwrap_or_default();
        Ok(location.map(GotoDefinitionResponse::Scalar))
    }

    async fn rename(&self, params: RenameParams) -> Result<Option<WorkspaceEdit>> {
        let uri = params.text_document_position.text_document.uri;
        let position = params.text_document_position.position;
        let new_name = params.new_name;
        let source = self
            .documents
            .lock()
            .unwrap()
            .get(&uri)
            .cloned()
            .or_else(|| {
                uri.to_file_path()
                    .ok()
                    .and_then(|path| std::fs::read_to_string(path).ok())
            });
        let Some(source) = source else {
            return Ok(None);
        };
        let base_dir = uri.to_file_path().ok().and_then(|path| {
            if path.is_dir() {
                Some(path)
            } else {
                path.parent().map(|parent| parent.to_path_buf())
            }
        });
        let options = self.source_options(base_dir.as_deref());
        let uri_for_task = uri.clone();
        let workspace_edit = tokio::task::spawn_blocking(move || {
            rename_for_source(uri_for_task, &source, base_dir, options, position, &new_name)
        })
        .await
        .unwrap_or_default();
        Ok(workspace_edit)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn document_symbols_include_top_level_declarations() {
        let symbols = document_symbols(
            "pub struct point { x: int }\n\
             pub enum result 'ok 'err:\n  ok 'ok\n  err 'err\n\
             pub act fs:\n  read: str -> opt str\n\
             pub role Display 'a:\n  our a.show: str\n\
             my norm2 p = p.x * p.x\n\
             pub prefix(fail) 1.0.0 = \\e -> e.throw\n",
        );
        let names = symbols
            .iter()
            .map(|symbol| (symbol.name.as_str(), symbol.kind))
            .collect::<Vec<_>>();
        assert!(names.contains(&("point", SymbolKind::STRUCT)));
        assert!(names.contains(&("result", SymbolKind::ENUM)));
        assert!(names.contains(&("fs", SymbolKind::INTERFACE)));
        assert!(names.contains(&("Display", SymbolKind::INTERFACE)));
        assert!(names.contains(&("norm2", SymbolKind::FUNCTION)));
        assert!(names.contains(&("fail", SymbolKind::OPERATOR)));
    }

    #[test]
    fn document_symbols_account_for_leading_comments() {
        let symbols = document_symbols("// comment\n\nmy value = 1\n");
        let value = symbols
            .iter()
            .find(|symbol| symbol.name == "value")
            .expect("value symbol");
        assert_eq!(value.selection_range.start.line, 2);
        assert_eq!(value.selection_range.start.character, 3);
    }

    #[test]
    fn rename_replaces_local_binding_definition_and_uses() {
        let source = "my foo = 1\nmy bar = foo + foo\n";
        let uri = Url::parse("file:///tmp/test.yu").unwrap();
        let edit = rename_for_source(
            uri.clone(),
            source,
            None,
            SourceOptions {
                std_root: None,
                implicit_prelude: false,
                search_paths: Vec::new(),
            },
            Position {
                line: 0,
                character: 3,
            },
            "renamed",
        )
        .expect("rename should return edits");

        let changes = edit.changes.expect("workspace edit should have changes");
        let edits = changes.get(&uri).expect("edits for entry file");
        assert_eq!(edits.len(), 3, "definition + two uses, got {edits:?}");
        let texts: Vec<&str> = edits.iter().map(|e| e.new_text.as_str()).collect();
        assert!(texts.iter().all(|t| *t == "renamed"));
        let ranges: Vec<(u32, u32)> = edits
            .iter()
            .map(|e| (e.range.start.line, e.range.start.character))
            .collect();
        assert!(ranges.contains(&(0, 3)), "def site: {ranges:?}");
        assert!(ranges.contains(&(1, 9)), "first use: {ranges:?}");
        assert!(ranges.contains(&(1, 15)), "second use: {ranges:?}");
    }

    #[test]
    fn rename_refuses_invalid_identifier() {
        let source = "my foo = 1\n";
        let uri = Url::parse("file:///tmp/test.yu").unwrap();
        let edit = rename_for_source(
            uri,
            source,
            None,
            SourceOptions {
                std_root: None,
                implicit_prelude: false,
                search_paths: Vec::new(),
            },
            Position {
                line: 0,
                character: 3,
            },
            "1bad",
        );
        assert!(edit.is_none(), "rename to '1bad' should be refused");
    }

    #[test]
    fn rename_refuses_when_def_lives_in_std() {
        // `each` is defined in lib/std/undet.yu, so renaming it from the entry file
        // must refuse to avoid rewriting library sources.
        let source = "my a = each [1, 2, 3]\n";
        let uri = Url::parse("file:///tmp/test.yu").unwrap();
        let edit = rename_for_source(
            uri,
            source,
            None,
            std_source_options(),
            position_of(source, "each").expect("each position"),
            "every",
        );
        assert!(
            edit.is_none(),
            "rename of `each` (defined in std) must be refused"
        );
    }

    #[test]
    fn goto_definition_jumps_to_local_binding() {
        let source = "my foo = 1\nmy bar = foo + 2\n";
        let uri = Url::parse("file:///tmp/test.yu").unwrap();
        let location = goto_definition_for_source(
            uri.clone(),
            source,
            None,
            SourceOptions {
                std_root: None,
                implicit_prelude: false,
                search_paths: Vec::new(),
            },
            Position {
                // `foo` on the RHS of bar (line 1, character 9)
                line: 1,
                character: 9,
            },
        )
        .expect("goto definition for foo use site");
        assert_eq!(location.uri, uri);
        // `my foo = 1` — the `foo` ident starts at line 0, byte 3.
        assert_eq!(location.range.start.line, 0);
        assert_eq!(location.range.start.character, 3);
    }

    #[test]
    fn hover_accounts_for_leading_comments_without_offset_patch() {
        let source = "// comment\n\nmy value = 1\n";
        let hover = hover_for_source(
            source,
            None,
            SourceOptions {
                std_root: None,
                implicit_prelude: false,
                search_paths: Vec::new(),
            },
            Position {
                line: 2,
                character: 3,
            },
        )
        .expect("hover");
        let HoverContents::Markup(content) = hover.contents else {
            panic!("hover should use markdown");
        };
        assert!(content.value.contains("value: int"));
    }

    #[test]
    fn hover_accounts_for_leading_comments_with_implicit_prelude() {
        let source = "// comment\n\nmy value = 1\nmy a = each [1, 2, 3]\n";
        let hover = hover_for_source(
            source,
            None,
            std_source_options(),
            Position {
                line: 2,
                character: 3,
            },
        )
        .expect("hover");
        let HoverContents::Markup(content) = hover.contents else {
            panic!("hover should use markdown");
        };
        assert!(content.value.contains("value: int"));

        let hover = hover_for_source(
            source,
            None,
            std_source_options(),
            Position {
                line: 3,
                character: 7,
            },
        )
        .expect("hover");
        let HoverContents::Markup(content) = hover.contents else {
            panic!("hover should use markdown");
        };
        assert!(content.value.contains("each:"));
    }

    #[test]
    fn hover_shows_rendered_top_level_type() {
        let source = "my id x = x\n";
        let hover = hover_for_source(
            source,
            None,
            SourceOptions {
                std_root: None,
                implicit_prelude: false,
                search_paths: Vec::new(),
            },
            Position {
                line: 0,
                character: 3,
            },
        )
        .expect("hover");
        let HoverContents::Markup(content) = hover.contents else {
            panic!("hover should use markdown");
        };
        assert!(content.value.contains("id:"));
        assert!(content.value.contains("α -> α"));
    }

    #[test]
    fn hover_resolves_qualified_path_tail() {
        let source = "enum maybe:\n  just int\n  nil\n\nmy x = maybe::nil\n";
        let hover = hover_for_source(
            source,
            None,
            SourceOptions {
                std_root: None,
                implicit_prelude: false,
                search_paths: Vec::new(),
            },
            Position {
                line: 4,
                character: 14,
            },
        )
        .expect("hover");
        let HoverContents::Markup(content) = hover.contents else {
            panic!("hover should use markdown");
        };
        assert!(content.value.contains("maybe::nil:"));
        assert!(content.value.contains("maybe"));
    }

    #[test]
    fn hover_uses_resolved_local_reference_not_global_name() {
        let source = "my x = 1\nmy f x = x\n";
        let hover = hover_for_source(
            source,
            None,
            SourceOptions {
                std_root: None,
                implicit_prelude: false,
                search_paths: Vec::new(),
            },
            Position {
                line: 1,
                character: 9,
            },
        )
        .expect("hover");
        let HoverContents::Markup(content) = hover.contents else {
            panic!("hover should use markdown");
        };
        assert!(content.value.contains("x:"));
        assert!(content.value.contains("x: α"));
        assert!(!content.value.contains("->"));
        assert!(!content.value.contains("int"));
    }

    #[test]
    fn hover_uses_resolved_local_definition_not_global_name() {
        let source = "my x = 1\nmy f x = x\n";
        let hover = hover_for_source(
            source,
            None,
            SourceOptions {
                std_root: None,
                implicit_prelude: false,
                search_paths: Vec::new(),
            },
            Position {
                line: 1,
                character: 5,
            },
        )
        .expect("hover");
        let HoverContents::Markup(content) = hover.contents else {
            panic!("hover should use markdown");
        };
        assert!(content.value.contains("x:"));
        assert!(content.value.contains("x: α"));
        assert!(!content.value.contains("->"));
        assert!(!content.value.contains("int"));
    }

    #[test]
    fn hover_source_map_ignores_implicit_prelude_spans() {
        let source = "my x = 1\nmy f x = x\n";
        let hover = hover_for_source(
            source,
            None,
            SourceOptions {
                std_root: None,
                implicit_prelude: true,
                search_paths: Vec::new(),
            },
            Position {
                line: 1,
                character: 9,
            },
        )
        .expect("hover");
        let HoverContents::Markup(content) = hover.contents else {
            panic!("hover should use markdown");
        };
        assert!(content.value.contains("x: α"));
        assert!(!content.value.contains("->"));
        assert!(!content.value.contains("std::"));
    }

    #[test]
    fn hover_uses_parameter_definition_inside_multi_arg_binding_header() {
        let source = "my bound start stop = start\n";
        let hover = hover_for_source(
            source,
            None,
            SourceOptions {
                std_root: None,
                implicit_prelude: true,
                search_paths: Vec::new(),
            },
            Position {
                line: 0,
                character: 10,
            },
        )
        .expect("hover");
        let HoverContents::Markup(content) = hover.contents else {
            panic!("hover should use markdown");
        };
        assert!(content.value.contains("start: α"));
        assert!(!content.value.contains("->"));
    }

    #[test]
    fn hover_does_not_show_value_type_on_type_annotation_name() {
        let source = "my bound start: int = start\n";
        let hover = hover_for_source(
            source,
            None,
            SourceOptions {
                std_root: None,
                implicit_prelude: true,
                search_paths: Vec::new(),
            },
            Position {
                line: 0,
                character: 16,
            },
        );
        assert!(hover.is_none());
    }

    #[test]
    fn hover_uses_annotated_parameter_reference_not_binding_function_type() {
        let source = "pub exclusive(start: int, end: int): range = range::within (bound::excluded start, bound::excluded end)\n";
        let hover = hover_for_source(
            source,
            None,
            SourceOptions {
                std_root: None,
                implicit_prelude: true,
                search_paths: Vec::new(),
            },
            position_of(source, "start,").expect("body start position"),
        )
        .expect("hover");
        let HoverContents::Markup(content) = hover.contents else {
            panic!("hover should use markdown");
        };
        assert!(content.value.contains("start: int"));
        assert!(!content.value.contains("->"));
        assert!(!content.value.contains("range"));
    }

    #[test]
    fn hover_source_spans_account_for_implicit_prelude_prefix() {
        let source = "pub exclusive(start: int, end: int): range = range::within (bound::excluded start, bound::excluded end)\n";
        let std_root = resolve_or_install_std_root(None, None)
            .expect("stdlib root resolution")
            .expect("stdlib root");
        let hover = hover_for_source(
            source,
            None,
            SourceOptions {
                std_root: Some(std_root),
                implicit_prelude: true,
                search_paths: Vec::new(),
            },
            position_of(source, "start,").expect("body start position"),
        )
        .expect("hover");
        let HoverContents::Markup(content) = hover.contents else {
            panic!("hover should use markdown");
        };
        assert!(content.value.contains("start: int"));
        assert!(!content.value.contains("->"));
        assert!(!content.value.contains("range"));
    }

    #[test]
    fn hover_resolves_implicit_prelude_each_reference() {
        let source = "my a = each [1, 2, 3]\n";
        let hover = hover_for_source(
            source,
            None,
            std_source_options(),
            position_of(source, "each").expect("each position"),
        )
        .expect("hover");
        let HoverContents::Markup(content) = hover.contents else {
            panic!("hover should use markdown");
        };
        assert!(content.value.contains("each:"));
        assert!(content.value.contains("Fold<"));
        assert!(content.value.contains("std::undet::undet"));
    }

    #[test]
    fn hover_resolves_implicit_prelude_guard_colon_reference() {
        let source = "my a = each [1, 2, 3]\nguard: a > 1\n";
        let hover = hover_for_source(
            source,
            None,
            std_source_options(),
            position_of(source, "guard").expect("guard position"),
        )
        .expect("hover");
        let HoverContents::Markup(content) = hover.contents else {
            panic!("hover should use markdown");
        };
        assert!(content.value.contains("guard: bool"));
        assert!(content.value.contains("std::undet::undet"));
    }

    #[test]
    fn hover_resolves_method_selection() {
        let source = "{ each [1, 2, 3] }.once\n";
        let hover = hover_for_source(
            source,
            None,
            std_source_options(),
            position_of(source, "once").expect("once position"),
        )
        .expect("hover");
        let HoverContents::Markup(content) = hover.contents else {
            panic!("hover should use markdown");
        };
        assert!(content.value.contains("once:"));
        assert!(content.value.contains("undet"));
        assert!(content.value.contains("opt"));
        assert!(!content.value.contains("α & β"));
        assert!(!content.value.contains("ζ | η"));
    }

    #[test]
    fn hover_resolves_effect_method_selection_as_function_type() {
        let source = "{ each [1, 2, 3] }.list\n";
        let hover = hover_for_source(
            source,
            None,
            std_source_options(),
            position_of(source, "list").expect("list position"),
        )
        .expect("hover");
        let HoverContents::Markup(content) = hover.contents else {
            panic!("hover should use markdown");
        };
        assert!(content.value.contains("list:"));
        assert!(content.value.contains("undet"));
        assert!(content.value.contains("list<α>"));
        assert!(!content.value.contains("α & β"));
        assert!(!content.value.contains("ζ | η"));
    }

    #[test]
    fn hover_compacts_local_with_owner_context() {
        let source = "{\n    my a = each [1, 2, 3]\n    guard: a > 1\n    a\n}.once\n";
        let hover = hover_for_source(
            source,
            None,
            std_source_options(),
            Position {
                line: 2,
                character: 11,
            },
        )
        .expect("hover");
        let HoverContents::Markup(content) = hover.contents else {
            panic!("hover should use markdown");
        };
        assert!(content.value.contains("a: int"));
        assert!(!content.value.contains('|'));
    }

    #[test]
    fn diagnostics_include_runtime_type_mismatch_related_information() {
        let source = "my f(x: int) = x\nf true\n";
        let uri = Url::parse("file:///diagnostics.yu").expect("test uri");
        let int = test_named_type("int");
        let bool = test_named_type("bool");
        let evidence = typed_ir::PrincipalEvidence {
            expected_edges: vec![
                typed_ir::ExpectedEdgeEvidence {
                    id: 1,
                    kind: typed_ir::ExpectedEdgeKind::Annotation,
                    source_range: Some(test_source_range(source, "int")),
                    actual: typed_ir::TypeBounds::exact(int.clone()),
                    expected: typed_ir::TypeBounds::exact(int.clone()),
                    actual_effect: None,
                    expected_effect: None,
                    closed: true,
                    informative: true,
                    runtime_usable: true,
                },
                typed_ir::ExpectedEdgeEvidence {
                    id: 2,
                    kind: typed_ir::ExpectedEdgeKind::ApplicationArgument,
                    source_range: Some(test_source_range(source, "true")),
                    actual: typed_ir::TypeBounds::exact(bool.clone()),
                    expected: typed_ir::TypeBounds::exact(int.clone()),
                    actual_effect: None,
                    expected_effect: None,
                    closed: true,
                    informative: true,
                    runtime_usable: true,
                },
            ],
            ..Default::default()
        };
        let error = runtime::RuntimeError::TypeMismatch {
            expected: int,
            actual: bool,
            source: runtime::TypeSource::ApplyEvidence,
            context: Some(runtime::diagnostic::TypeMismatchContext {
                callee: None,
                phase: runtime::diagnostic::TypeMismatchPhase::ApplyArgument,
                callee_source_edge: Some(1),
                arg_source_edge: Some(2),
            }),
        };
        let diagnostic =
            runtime_error_to_lsp(&uri, source, source, &evidence, &error).expect("diagnostic");

        assert!(
            diagnostic.message.contains("type mismatch"),
            "{diagnostic:?}"
        );
        assert!(
            diagnostic.message.contains("expected int"),
            "{diagnostic:?}"
        );
        assert!(diagnostic.message.contains("got bool"), "{diagnostic:?}");
        assert_eq!(
            diagnostic.range.start,
            position_of(source, "true").expect("true position")
        );
        let related = diagnostic
            .related_information
            .as_ref()
            .expect("related information");
        assert!(
            related
                .iter()
                .any(|info| info.message.contains("actual type here is `bool`")
                    && info.message.contains("application argument")
                    && info.location.range.start
                        == position_of(source, "true").expect("true position")),
            "{related:?}"
        );
        assert!(
            related
                .iter()
                .any(|info| info.message.contains("expected type here is `int`")
                    && info.message.contains("annotation")),
            "{related:?}"
        );
    }

    #[test]
    fn diagnostics_include_non_function_application() {
        let source = "my a = 1 2\n";
        let uri = Url::parse("file:///diagnostics.yu").expect("test uri");
        let lowered = lower_virtual_source_with_options(
            source,
            None,
            SourceOptions {
                std_root: None,
                implicit_prelude: false,
                search_paths: Vec::new(),
            },
        )
        .expect("lowered source");
        let diagnostics = diagnostics_for_lowered_source(&uri, source, lowered);
        let diagnostic = diagnostics
            .iter()
            .find(|diagnostic| diagnostic.message == "expected function")
            .expect("non-function application diagnostic");

        assert_eq!(
            diagnostic.range.start,
            position_of(source, "2").expect("argument position")
        );
        let related = diagnostic
            .related_information
            .as_ref()
            .expect("related information");
        assert!(
            related
                .iter()
                .any(|info| info.message.contains("literal `1`")
                    && info.location.range.start
                        == position_of(source, "1").expect("callee position")),
            "{related:?}"
        );
    }

    fn std_source_options() -> SourceOptions {
        SourceOptions {
            std_root: resolve_or_install_std_root(None, None)
                .expect("stdlib root resolution")
                .or_else(|| Some(PathBuf::from("crates/yulang-sources/std"))),
            implicit_prelude: true,
            search_paths: Vec::new(),
        }
    }

    fn position_of(source: &str, needle: &str) -> Option<Position> {
        let offset = source.find(needle)?;
        Some(byte_to_position(&line_starts(source), offset))
    }

    fn test_source_range(source: &str, needle: &str) -> typed_ir::SourceRange {
        let start = source.find(needle).expect("source range start") as u32;
        typed_ir::SourceRange {
            start,
            end: start + needle.len() as u32,
        }
    }

    fn test_named_type(name: &str) -> typed_ir::Type {
        typed_ir::Type::Named {
            path: typed_ir::Path::from_name(typed_ir::Name(name.to_string())),
            args: Vec::new(),
        }
    }

    #[test]
    fn hover_uses_parameter_reference_inside_multi_arg_binding_body() {
        let source = "my bound start stop = start\n";
        let hover = hover_for_source(
            source,
            None,
            SourceOptions {
                std_root: None,
                implicit_prelude: true,
                search_paths: Vec::new(),
            },
            Position {
                line: 0,
                character: 24,
            },
        )
        .expect("hover");
        let HoverContents::Markup(content) = hover.contents else {
            panic!("hover should use markdown");
        };
        assert!(content.value.contains("start: α"));
        assert!(!content.value.contains("->"));
    }

    #[test]
    fn hover_does_not_fallback_to_same_named_global_for_unknown_bare_ident() {
        let source = "my start x = x\nmy probe = missing\n";
        let hover = hover_for_source(
            source,
            None,
            SourceOptions {
                std_root: None,
                implicit_prelude: false,
                search_paths: Vec::new(),
            },
            Position {
                line: 1,
                character: 11,
            },
        );
        assert!(hover.is_none());
    }
}

async fn serve() {
    let std_root = std::env::var_os(yulang_sources::YULANG_STD_ENV)
        .map(PathBuf::from)
        .filter(|root| is_std_root(root));

    let stdin = tokio::io::stdin();
    let stdout = tokio::io::stdout();

    let (service, socket) = LspService::new(|client| Backend {
        client,
        std_root,
        documents: Mutex::new(HashMap::new()),
    });
    Server::new(stdin, stdout, socket).serve(service).await;
}

pub fn run_blocking() {
    let runtime = tokio::runtime::Builder::new_multi_thread()
        .enable_all()
        .build()
        .expect("failed to create tokio runtime for Yulang language server");
    runtime.block_on(serve());
}
