use std::collections::HashMap;
use std::path::PathBuf;
use std::sync::Mutex;

use tower_lsp::jsonrpc::Result;
use tower_lsp::lsp_types::*;
use tower_lsp::{Client, LanguageServer, LspService, Server};
use yulang_editor::semantic_tokens;
use yulang_infer::simplify::compact::compact_type_var;
use yulang_infer::{
    DefId, LowerState, Name as InferName, Path as InferPath, collect_compact_results_for_paths,
    collect_surface_diagnostics, format_coalesced_scheme, lower_virtual_source_with_options,
    surface_diagnostic::SurfaceDiagnostic,
};
use yulang_parser::lex::SyntaxKind;
use yulang_parser::sink::YulangLanguage;
use yulang_sources::{
    SourceOptions, collect_virtual_source_files_with_options, is_std_root,
    resolve_or_install_std_root,
};

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

fn byte_range_with_offset_to_lsp(
    line_starts: &[usize],
    span: rowan::TextRange,
    offset: usize,
) -> Range {
    let start = usize::from(span.start()) + offset;
    let end = usize::from(span.end()) + offset;
    Range {
        start: byte_to_position(line_starts, start),
        end: byte_to_position(line_starts, end),
    }
}

fn leading_trivia_len(text: &str) -> usize {
    let bytes = text.as_bytes();
    let mut pos = 0;
    loop {
        while pos < bytes.len() && matches!(bytes[pos], b' ' | b'\t' | b'\r' | b'\n') {
            pos += 1;
        }
        if pos + 1 < bytes.len() && bytes[pos] == b'/' && bytes[pos + 1] == b'/' {
            while pos < bytes.len() && bytes[pos] != b'\n' {
                pos += 1;
            }
            continue;
        }
        if pos + 1 < bytes.len() && bytes[pos] == b'/' && bytes[pos + 1] == b'*' {
            pos += 2;
            while pos + 1 < bytes.len() {
                if bytes[pos] == b'*' && bytes[pos + 1] == b'/' {
                    pos += 2;
                    break;
                }
                pos += 1;
            }
            continue;
        }
        break;
    }
    pos
}

fn document_symbols(source: &str) -> Vec<DocumentSymbol> {
    let green = yulang_parser::parse_module_to_green(source);
    let root = SyntaxNode::new_root(green);
    let line_starts = line_starts(source);
    let leading = leading_trivia_len(source);
    root.children()
        .filter_map(|node| document_symbol_for_node(&node, &line_starts, leading))
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
    let leading = leading_trivia_len(source);
    let green = yulang_parser::parse_module_to_green(source);
    let root = SyntaxNode::new_root(green);

    let tokens = root
        .descendants_with_tokens()
        .filter_map(|it| it.into_token())
        .filter(|token| is_hover_name_token(token) || token.kind() == SyntaxKind::ColonColon)
        .map(|token| {
            let syntax_range = token.text_range();
            let range = byte_range_with_offset_to_lsp(&line_starts, syntax_range, leading);
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
        SyntaxKind::Ident | SyntaxKind::SigilIdent | SyntaxKind::OpName
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

    if let Some(def) = resolve_hover_target_source_def(state, target) {
        return hover_type_for_def(state, def);
    }

    if let Some(def) = resolve_hover_target_def(state, target) {
        return hover_type_for_def(state, def);
    }

    None
}

fn resolve_hover_target_source_def(state: &LowerState, target: &HoverTarget) -> Option<DefId> {
    state
        .value_use_spans
        .iter()
        .rev()
        .find_map(|(span, def)| span_contains_range(*span, target.syntax_range).then_some(*def))
        .or_else(|| {
            state.ref_spans.iter().find_map(|(ref_id, span)| {
                span_contains_range(*span, target.syntax_range)
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
    state
        .def_spans
        .iter()
        .filter(|(_, span)| span_contains_range(**span, target))
        .min_by_key(|(_, span)| usize::from(span.end()) - usize::from(span.start()))
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
    if let Some(result) = collect_compact_results_for_paths(state, &paths)
        .into_iter()
        .next()
    {
        return Some(result);
    }
    let name = state.def_name(def)?.0.clone();
    let scheme = state.compact_scheme_of(def).or_else(|| {
        state
            .def_tvs
            .get(&def)
            .map(|tv| compact_type_var(&state.infer, *tv))
    })?;
    Some((name, format_coalesced_scheme(&scheme)))
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

fn document_symbol_for_node(
    node: &SyntaxNode,
    line_starts: &[usize],
    leading: usize,
) -> Option<DocumentSymbol> {
    let spec = symbol_spec(node)?;
    let name_token = symbol_name_token(node, spec.name_kind);
    let name = name_token
        .as_ref()
        .map(|token| token.text().to_string())
        .or_else(|| spec.fallback_name)?;
    let range = byte_range_with_offset_to_lsp(line_starts, node.text_range(), leading);
    let selection_range = name_token
        .map(|token| byte_range_with_offset_to_lsp(line_starts, token.text_range(), leading))
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

    fn position_of(source: &str, needle: &str) -> Option<Position> {
        let offset = source.find(needle)?;
        Some(byte_to_position(&line_starts(source), offset))
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
