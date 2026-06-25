//! 新ソース収集層。ファイル別 op テーブルを正しく組んでフルパースするのが目的。
//! まずは先読み（`parse_header_to_green` → CST から use/op を抽出）から積む。

use parser::lex::SyntaxKind;
use parser::op::{BpVec, OpDef, OpTable, standard_op_table};
use parser::sink::YulangLanguage;
use rowan::{GreenNode, NodeOrToken, SyntaxNode};
use serde::{Deserialize, Serialize};
use std::collections::HashMap;

mod realm;

pub use realm::{
    FreezeRealmError, FreezeRealmOutput, FrozenRealmSnapshot, FrozenRealmSnapshotFile,
    RealmIdentity, RealmManifestError, RealmVersion, ResolvedRealmId, SourceRealmDependency,
    SourceRealmManifest, SourceRealmRoot, YULANG_LOCK_FILE, YULANG_MANIFEST_FILE,
    YULANG_PROJECT_DIR, freeze_realm_version, load_realm_manifest, local_realm_id,
    local_realm_root,
};

// ── 基礎型（source loader と parser input の共有語彙）──────────────────────

#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct Name(pub String);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct SourceRange {
    pub start: usize,
    pub end: usize,
}

#[derive(Debug, Clone, Default, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct Path {
    pub segments: Vec<Name>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum Visibility {
    Pub,
    Our,
    My,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum UseImport {
    /// `use a::b::c` / `use a::b as c`
    Alias { name: Name, path: Path },
    /// `use a::b::*`
    Glob { prefix: Path },
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct UseDecl {
    pub visibility: Visibility,
    pub import: UseImport,
}

/// 外部 module ファイルを読むきっかけになる構文。
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum ModuleLoadKind {
    /// `mod foo;`
    ModDecl,
    /// `use mod foo::bar`
    UseMod,
}

/// header 先読みで取れる module load directive。
///
/// header は `use` / `op` だけを先読みする入口なので、ここには `use mod foo::...`
/// の先頭 module 名だけを残す。`mod foo;` はフルパース後の
/// [`module_load_requests`] で拾う。実際の親 module path は
/// `LoadedFile::module_loads` 側で付く。
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct ModuleLoadDirective {
    pub name: Name,
    pub kind: ModuleLoadKind,
    pub visibility: Visibility,
}

/// 外部 module ファイルを読む要求。
///
/// `parent` はこの要求が現れた inline module の path、`name` はその直下に生える子 module 名。
/// たとえば root module 内の `mod foo;` は `parent = []`, `name = foo`。
/// `mod outer: mod inner;` は `parent = [outer]`, `name = inner`。
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct ModuleLoadRequest {
    pub parent: Path,
    pub name: Name,
    pub kind: ModuleLoadKind,
    pub visibility: Visibility,
}

impl ModuleLoadRequest {
    pub fn module_path(&self) -> Path {
        let mut segments = self.parent.segments.clone();
        segments.push(self.name.clone());
        Path { segments }
    }
}

/// ファイル先頭で宣言された演算子（他ファイルへの export 候補）。
#[derive(Debug, Clone)]
pub struct OpExport {
    pub visibility: Visibility,
    pub name: Name,
    pub op: OpDef,
}

/// 先読みの成果。本体パース前に取れる use と op。
#[derive(Debug, Clone, Default)]
pub struct Header {
    pub uses: Vec<UseDecl>,
    pub ops: Vec<OpExport>,
    pub module_loads: Vec<ModuleLoadDirective>,
}

#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct CompiledSyntaxSurface {
    pub files: Vec<CompiledSyntaxFile>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CompiledSyntaxMergeError {
    ConflictingOperator { module_path: Path, name: Name },
}

impl CompiledSyntaxSurface {
    pub fn from_loaded_files(files: &[LoadedFile]) -> Self {
        Self {
            files: files
                .iter()
                .map(CompiledSyntaxFile::from_loaded_file)
                .collect(),
        }
    }

    pub fn merge_prefixes<'a>(
        prefixes: impl IntoIterator<Item = &'a CompiledSyntaxSurface>,
    ) -> Result<Self, CompiledSyntaxMergeError> {
        let mut files = Vec::<CompiledSyntaxFile>::new();
        for prefix in prefixes {
            for file in &prefix.files {
                merge_compiled_syntax_file(&mut files, file)?;
            }
        }
        files.sort_by_key(compiled_syntax_file_order);
        Ok(Self { files })
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct CompiledSyntaxFile {
    pub module_path: Path,
    pub uses: Vec<UseDecl>,
    pub ops: Vec<CompiledOpExport>,
    pub module_loads: Vec<ModuleLoadRequest>,
}

impl CompiledSyntaxFile {
    fn from_loaded_file(file: &LoadedFile) -> Self {
        Self {
            module_path: file.module_path.clone(),
            uses: file
                .header
                .uses
                .iter()
                .filter(|decl| exports_across_unit_boundary(decl.visibility))
                .cloned()
                .collect(),
            ops: file
                .header
                .ops
                .iter()
                .filter(|decl| exports_across_unit_boundary(decl.visibility))
                .map(CompiledOpExport::from_op_export)
                .collect(),
            module_loads: file.module_loads.clone(),
        }
    }

    fn syntax_input(&self) -> SyntaxFileInput {
        SyntaxFileInput {
            module_path: self.module_path.clone(),
            header: Header {
                uses: self.uses.clone(),
                ops: self
                    .ops
                    .iter()
                    .map(CompiledOpExport::to_op_export)
                    .collect(),
                module_loads: Vec::new(),
            },
        }
    }
}

fn merge_compiled_syntax_file(
    files: &mut Vec<CompiledSyntaxFile>,
    file: &CompiledSyntaxFile,
) -> Result<(), CompiledSyntaxMergeError> {
    let Some(existing) = files
        .iter_mut()
        .find(|existing| existing.module_path == file.module_path)
    else {
        files.push(file.clone());
        return Ok(());
    };

    for use_decl in &file.uses {
        push_unique(&mut existing.uses, use_decl.clone());
    }
    for op in &file.ops {
        merge_compiled_op_export(existing, &file.module_path, op)?;
    }
    for request in &file.module_loads {
        push_unique(&mut existing.module_loads, request.clone());
    }
    Ok(())
}

fn merge_compiled_op_export(
    existing: &mut CompiledSyntaxFile,
    module_path: &Path,
    op: &CompiledOpExport,
) -> Result<(), CompiledSyntaxMergeError> {
    if existing.ops.iter().any(|existing| existing == op) {
        return Ok(());
    }
    if existing
        .ops
        .iter()
        .any(|existing| existing.name == op.name && existing.visibility == op.visibility)
    {
        return Err(CompiledSyntaxMergeError::ConflictingOperator {
            module_path: module_path.clone(),
            name: op.name.clone(),
        });
    }
    existing.ops.push(op.clone());
    Ok(())
}

fn push_unique<T: PartialEq>(items: &mut Vec<T>, item: T) {
    if !items.contains(&item) {
        items.push(item);
    }
}

fn compiled_syntax_file_order(file: &CompiledSyntaxFile) -> (usize, Vec<String>) {
    (
        file.module_path.segments.len(),
        file.module_path
            .segments
            .iter()
            .map(|segment| segment.0.clone())
            .collect(),
    )
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct CompiledOpExport {
    pub visibility: Visibility,
    pub name: Name,
    pub op: CompiledOpDef,
}

impl CompiledOpExport {
    fn from_op_export(export: &OpExport) -> Self {
        Self {
            visibility: export.visibility,
            name: export.name.clone(),
            op: CompiledOpDef::from_op_def(&export.op),
        }
    }

    fn to_op_export(&self) -> OpExport {
        OpExport {
            visibility: self.visibility,
            name: self.name.clone(),
            op: self.op.to_op_def(),
        }
    }
}

#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct CompiledOpDef {
    pub prefix: Option<Vec<i8>>,
    pub infix: Option<(Vec<i8>, Vec<i8>)>,
    pub suffix: Option<Vec<i8>>,
    pub nullfix: bool,
}

impl CompiledOpDef {
    fn from_op_def(op: &OpDef) -> Self {
        Self {
            prefix: op.prefix.as_ref().map(bp_to_vec),
            infix: op
                .infix
                .as_ref()
                .map(|(left, right)| (bp_to_vec(left), bp_to_vec(right))),
            suffix: op.suffix.as_ref().map(bp_to_vec),
            nullfix: op.nullfix,
        }
    }

    fn to_op_def(&self) -> OpDef {
        OpDef {
            prefix: self
                .prefix
                .as_ref()
                .map(|parts| BpVec::from_parts(parts.clone())),
            infix: self.infix.as_ref().map(|(left, right)| {
                (
                    BpVec::from_parts(left.clone()),
                    BpVec::from_parts(right.clone()),
                )
            }),
            suffix: self
                .suffix
                .as_ref()
                .map(|parts| BpVec::from_parts(parts.clone())),
            nullfix: self.nullfix,
        }
    }
}

#[derive(Clone)]
struct SyntaxFileInput {
    module_path: Path,
    header: Header,
}

// ── 先読み ──────────────────────────────────────────────────────────────

/// ソースの先頭から use / op 宣言だけを読み取る。body には踏み込まない
/// （[`parser::parse_header_to_green`] が最初の定義文で停止する）。
pub fn read_header(source: &str) -> Header {
    let green = parser::parse_header_to_green(source);
    let root = SyntaxNode::<YulangLanguage>::new_root(green);
    let mut header = Header::default();
    for node in root.children() {
        match node.kind() {
            SyntaxKind::UseDecl => {
                let visibility = visibility_of(&node);
                for import in use_imports(&node) {
                    header.uses.push(UseDecl { visibility, import });
                }
                if let Some(name) = use_mod_load_name(&node) {
                    header.module_loads.push(ModuleLoadDirective {
                        name,
                        kind: ModuleLoadKind::UseMod,
                        visibility,
                    });
                }
            }
            SyntaxKind::OpDef => {
                if let Some(op) = op_export(&node) {
                    header.ops.push(op);
                }
            }
            _ => {}
        }
    }
    header
}

/// フルパース済み module CST から、外部 module load request を集める。
///
/// `mod foo;` と `use mod foo::bar` だけが request を出す。
///
/// plain `use foo::bar` は既に存在する module namespace の参照なので、ファイル読み込み
/// 要求にはしない。`use realm/band::module` 系は manifest / lock に基づく source
/// dependency import と通常の `use` の合成なので、local module tree を育てる
/// [`ModuleLoadRequest`] とは別の request として扱う。
pub fn module_load_requests(
    module_path: &Path,
    root: &SyntaxNode<YulangLanguage>,
) -> Vec<ModuleLoadRequest> {
    let mut out = Vec::new();
    collect_module_load_requests(root, module_path, &mut out);
    out
}

// ── use 抽出（旧 use_decl_imports の最小版。realm/anchor/without は後で）──

pub fn use_imports(node: &SyntaxNode<YulangLanguage>) -> Vec<UseImport> {
    let mut collector = UseImportCollector::new(Vec::new());
    collector.collect_node(node);
    collector.finish()
}

struct UseImportCollector {
    imports: Vec<UseImport>,
    path: Vec<Name>,
    base_len: usize,
    alias: Option<Name>,
    after_as: bool,
    paren_depth: usize,
}

impl UseImportCollector {
    fn new(prefix: Vec<Name>) -> Self {
        let base_len = prefix.len();
        Self {
            imports: Vec::new(),
            path: prefix,
            base_len,
            alias: None,
            after_as: false,
            paren_depth: 0,
        }
    }

    fn collect_node(&mut self, node: &SyntaxNode<YulangLanguage>) {
        for item in node.children_with_tokens() {
            match item {
                NodeOrToken::Node(child) => self.collect_child_node(&child),
                NodeOrToken::Token(tok) => self.collect_token(tok.kind(), tok.text()),
            }
        }
    }

    fn finish(mut self) -> Vec<UseImport> {
        self.push_alias_item();
        self.imports
    }

    fn collect_child_node(&mut self, child: &SyntaxNode<YulangLanguage>) {
        match child.kind() {
            SyntaxKind::BraceGroup => self.collect_group(child),
            SyntaxKind::Separator => self.finish_item(),
            _ => {}
        }
    }

    fn collect_group(&mut self, group: &SyntaxNode<YulangLanguage>) {
        let mut group_collector = UseImportCollector::new(self.path.clone());
        group_collector.collect_node(group);
        self.imports.extend(group_collector.finish());
        self.reset_item();
    }

    fn collect_token(&mut self, kind: SyntaxKind, text: &str) {
        match kind {
            SyntaxKind::As => self.after_as = true,
            SyntaxKind::ParenL => self.paren_depth += 1,
            SyntaxKind::ParenR => self.paren_depth = self.paren_depth.saturating_sub(1),
            SyntaxKind::OpName if text == "*" && self.paren_depth == 0 => {
                self.imports.push(UseImport::Glob {
                    prefix: Path {
                        segments: self.path.clone(),
                    },
                });
                self.reset_item();
            }
            SyntaxKind::Ident if self.after_as => {
                self.alias = Some(Name(text.to_string()));
                self.after_as = false;
            }
            SyntaxKind::Ident | SyntaxKind::OpName => {
                self.path.push(Name(text.to_string()));
                self.after_as = false;
            }
            // Pub/Our/My/Use/Mod/ColonColon/Slash/Brace/Comma 等は構造トークン。
            _ => {}
        }
    }

    fn finish_item(&mut self) {
        self.push_alias_item();
        self.reset_item();
    }

    fn push_alias_item(&mut self) {
        if self.path.len() <= self.base_len {
            return;
        }
        push_alias_import(&mut self.imports, self.path.clone(), self.alias.clone());
    }

    fn reset_item(&mut self) {
        self.path.truncate(self.base_len);
        self.alias = None;
        self.after_as = false;
        self.paren_depth = 0;
    }
}

fn collect_module_load_requests(
    block: &SyntaxNode<YulangLanguage>,
    module_path: &Path,
    out: &mut Vec<ModuleLoadRequest>,
) {
    for node in block.children() {
        match node.kind() {
            SyntaxKind::UseDecl => {
                if let Some(name) = use_mod_load_name(&node) {
                    out.push(ModuleLoadRequest {
                        parent: module_path.clone(),
                        name,
                        kind: ModuleLoadKind::UseMod,
                        visibility: visibility_of(&node),
                    });
                }
            }
            SyntaxKind::ModDecl => collect_mod_load_request(&node, module_path, out),
            _ => {}
        }
    }
}

fn collect_mod_load_request(
    node: &SyntaxNode<YulangLanguage>,
    module_path: &Path,
    out: &mut Vec<ModuleLoadRequest>,
) {
    let Some(name) = direct_token_text(node, SyntaxKind::Ident).map(Name) else {
        return;
    };
    if has_direct_token(node, SyntaxKind::Semicolon) {
        out.push(ModuleLoadRequest {
            parent: module_path.clone(),
            name,
            kind: ModuleLoadKind::ModDecl,
            visibility: visibility_of(node),
        });
        return;
    }

    let mut child_path = module_path.clone();
    child_path.segments.push(name);
    for child in node.children() {
        if matches!(
            child.kind(),
            SyntaxKind::BraceGroup | SyntaxKind::IndentBlock
        ) {
            collect_module_load_requests(&child, &child_path, out);
        }
    }
}

fn use_mod_load_name(node: &SyntaxNode<YulangLanguage>) -> Option<Name> {
    let mut after_mod = false;
    for item in node.children_with_tokens() {
        let NodeOrToken::Token(tok) = item else {
            continue;
        };
        match tok.kind() {
            SyntaxKind::Mod => after_mod = true,
            SyntaxKind::Ident if after_mod => return Some(Name(tok.text().to_string())),
            _ => {}
        }
    }
    None
}

fn push_alias_import(imports: &mut Vec<UseImport>, path: Vec<Name>, alias: Option<Name>) {
    let Some(last) = path.last().cloned() else {
        return;
    };
    let name = alias.unwrap_or(last);
    imports.push(UseImport::Alias {
        name,
        path: Path { segments: path },
    });
}

// ── op 抽出（旧 syntax_export / op_def_from_header の写経）───────────────────

fn op_export(node: &SyntaxNode<YulangLanguage>) -> Option<OpExport> {
    let header = node
        .children()
        .find(|child| child.kind() == SyntaxKind::OpDefHeader)?;
    let name = direct_token_text(&header, SyntaxKind::OpName).map(Name)?;
    let fixity = header.children_with_tokens().find_map(|item| match item {
        NodeOrToken::Token(tok)
            if matches!(
                tok.kind(),
                SyntaxKind::Prefix | SyntaxKind::Infix | SyntaxKind::Suffix | SyntaxKind::Nullfix
            ) =>
        {
            Some(tok.kind())
        }
        _ => None,
    })?;
    let bps = header
        .children_with_tokens()
        .filter_map(|item| match item {
            NodeOrToken::Token(tok) if tok.kind() == SyntaxKind::Number => BpVec::parse(tok.text()),
            _ => None,
        })
        .collect::<Vec<_>>();
    Some(OpExport {
        visibility: visibility_of(node),
        name,
        op: op_def_from_header(fixity, &bps),
    })
}

fn op_def_from_header(fixity: SyntaxKind, bps: &[BpVec]) -> OpDef {
    match fixity {
        SyntaxKind::Prefix => OpDef {
            prefix: bps.first().cloned(),
            ..OpDef::default()
        },
        SyntaxKind::Infix => OpDef {
            infix: bps.first().cloned().zip(bps.get(1).cloned()),
            ..OpDef::default()
        },
        SyntaxKind::Suffix => OpDef {
            suffix: bps.first().cloned(),
            ..OpDef::default()
        },
        SyntaxKind::Nullfix => OpDef {
            nullfix: true,
            ..OpDef::default()
        },
        _ => OpDef::default(),
    }
}

// ── 共通ヘルパ ──────────────────────────────────────────────────────────

/// 宣言ノード（または OpDefHeader 子）直下の visibility トークンを読む。
/// 無ければ `Our`（＝band 外からは見えない）を既定とする。
fn visibility_of(node: &SyntaxNode<YulangLanguage>) -> Visibility {
    fn direct(node: &SyntaxNode<YulangLanguage>) -> Option<Visibility> {
        node.children_with_tokens().find_map(|item| match item {
            NodeOrToken::Token(tok) => match tok.kind() {
                SyntaxKind::Pub => Some(Visibility::Pub),
                SyntaxKind::Our => Some(Visibility::Our),
                SyntaxKind::My => Some(Visibility::My),
                _ => None,
            },
            _ => None,
        })
    }
    direct(node)
        .or_else(|| {
            node.children()
                .find(|child| child.kind() == SyntaxKind::OpDefHeader)
                .and_then(|header| direct(&header))
        })
        .unwrap_or(Visibility::Our)
}

fn direct_token_text(node: &SyntaxNode<YulangLanguage>, kind: SyntaxKind) -> Option<String> {
    node.children_with_tokens().find_map(|item| match item {
        NodeOrToken::Token(tok) if tok.kind() == kind => Some(tok.text().to_string()),
        _ => None,
    })
}

fn has_direct_token(node: &SyntaxNode<YulangLanguage>, kind: SyntaxKind) -> bool {
    node.children_with_tokens()
        .any(|item| matches!(item, NodeOrToken::Token(tok) if tok.kind() == kind))
}

fn exports_across_unit_boundary(visibility: Visibility) -> bool {
    matches!(visibility, Visibility::Pub | Visibility::Our)
}

fn bp_to_vec(bp: &BpVec) -> Vec<i8> {
    bp.as_slice().to_vec()
}

// ── 複数ファイルの読み込み ──────────────────────────────────────────────
// 依存解決 → 実効 export op の不動点 → ファイル別初期テーブル → フルパース。
// 全段階が順序無関係（先読み独立／不動点収束／フルパース独立）＝SCC は不要。

/// 入力ファイル。`module_path` は収集層（FS を辿る上位層）が付けてくる前提。
#[derive(Debug, Clone)]
pub struct SourceFile {
    pub module_path: Path,
    pub source: String,
}

/// 先読み・op テーブル確定・フルパースまで済んだファイル。
#[derive(Debug, Clone)]
pub struct LoadedFile {
    pub module_path: Path,
    pub source: String,
    pub header: Header,
    /// `mod foo;` と `use mod foo::bar` から出た外部 module load request。
    pub module_loads: Vec<ModuleLoadRequest>,
    /// このファイルを打つのに使った op テーブル（standard + 輸入 op）。
    pub op_table: OpTable,
    pub cst: GreenNode,
}

/// 全ファイルを読み込む。op テーブルはファイル別に正しく組む（循環 use でも OK）。
pub fn load(files: Vec<SourceFile>) -> Vec<LoadedFile> {
    load_with_loaded_prefix(&[], files)
}

/// 既に load 済みの dependency prefix を再利用し、suffix だけをフルパースする。
///
/// `prefix` は `suffix` に依存しない dependency-closed な file set であることが前提。
/// この入口は compiled-unit artifact import の手前に置く軽量な process-local cache 境界で、
/// downstream file の op table は prefix の header / export surface から組み直す。
pub fn load_with_loaded_prefix(prefix: &[LoadedFile], suffix: Vec<SourceFile>) -> Vec<LoadedFile> {
    let prefix_inputs: Vec<SyntaxFileInput> = prefix
        .iter()
        .map(|file| SyntaxFileInput {
            module_path: file.module_path.clone(),
            header: file.header.clone(),
        })
        .collect();
    let mut loaded = Vec::with_capacity(prefix.len() + suffix.len());
    loaded.extend(prefix.iter().cloned());
    loaded.extend(load_suffix_after_syntax_prefix(&prefix_inputs, suffix));
    loaded
}

/// Serialized syntax artifacts provide the same parser-facing surface as an
/// already-loaded prefix, without requiring the dependency files' CSTs.
pub fn load_suffix_with_syntax_prefix(
    prefix: &CompiledSyntaxSurface,
    suffix: Vec<SourceFile>,
) -> Vec<LoadedFile> {
    let prefix_inputs = prefix
        .files
        .iter()
        .map(CompiledSyntaxFile::syntax_input)
        .collect::<Vec<_>>();
    load_suffix_after_syntax_prefix(&prefix_inputs, suffix)
}

fn load_suffix_after_syntax_prefix(
    prefix: &[SyntaxFileInput],
    suffix: Vec<SourceFile>,
) -> Vec<LoadedFile> {
    let n = prefix.len() + suffix.len();

    let suffix_headers: Vec<Header> = suffix
        .iter()
        .map(|file| read_header(&file.source))
        .collect();
    let headers: Vec<Header> = prefix
        .iter()
        .map(|file| file.header.clone())
        .chain(suffix_headers.iter().cloned())
        .collect();
    let module_paths: Vec<Path> = prefix
        .iter()
        .map(|file| file.module_path.clone())
        .chain(suffix.iter().map(|file| file.module_path.clone()))
        .collect();

    // 1. module_path → ファイル index
    let mut index: HashMap<Path, usize> = HashMap::with_capacity(n);
    for (i, module_path) in module_paths.iter().enumerate() {
        index.insert(module_path.clone(), i);
    }

    // 2. 自前 export op（先頭の pub/our op。my はファイル内のみ）
    let mut effective: Vec<HashMap<Name, OpDef>> = headers
        .iter()
        .map(|header| {
            let mut map = HashMap::new();
            for op in &header.ops {
                if matches!(op.visibility, Visibility::Pub | Visibility::Our) {
                    merge_into(&mut map, op.name.clone(), op.op.clone());
                }
            }
            map
        })
        .collect();

    // 3. pub/our use の再エクスポート連鎖を不動点で閉包（循環でも単調収束）
    loop {
        let mut changed = false;
        for i in 0..n {
            for use_decl in &headers[i].uses {
                // my use はローカル取り込みのみで、再エクスポートしない
                if matches!(use_decl.visibility, Visibility::My) {
                    continue;
                }
                let Some(j) = resolve_use(&use_decl.import, &index) else {
                    continue;
                };
                if i == j {
                    continue;
                }
                if merge_effective_exports(&mut effective, i, j) {
                    changed = true;
                }
            }
        }
        if !changed {
            break;
        }
    }

    // 4. prefix は既に full parse 済みなので再利用する。suffix は全体の export surface から
    //    初期テーブルを組んで full parse する。
    let mut loaded = Vec::with_capacity(suffix.len());
    for (offset, (file, header)) in suffix.into_iter().zip(suffix_headers).enumerate() {
        let i = prefix.len() + offset;
        let table = initial_op_table(i, &header, &index, &effective);
        let cst = parser::parse_module_to_green_with_ops(&file.source, table.clone());
        let root = SyntaxNode::<YulangLanguage>::new_root(cst.clone());
        let module_loads = module_load_requests(&file.module_path, &root);
        loaded.push(LoadedFile {
            module_path: file.module_path,
            source: file.source,
            header,
            module_loads,
            op_table: table,
            cst,
        });
    }
    loaded
}

/// 各ファイルの初期テーブル（standard + use 先の実効 export op）を作る。
/// 自前 op はフルパース中に parser が update_op_table するため、ここでは入れない。
fn initial_op_table(
    file_index: usize,
    header: &Header,
    index: &HashMap<Path, usize>,
    effective: &[HashMap<Name, OpDef>],
) -> OpTable {
    let mut table = standard_op_table();
    for use_decl in &header.uses {
        if let Some(import_index) = resolve_use(&use_decl.import, index) {
            if import_index == file_index {
                continue;
            }
            for (name, op) in &effective[import_index] {
                insert_op(&mut table, name.clone(), op.clone());
            }
        }
    }
    table
}

/// use の指す module_path を、最長 prefix マッチでファイル index に解決する。
fn resolve_use(import: &UseImport, index: &HashMap<Path, usize>) -> Option<usize> {
    let path = match import {
        UseImport::Alias { path, .. } => path,
        UseImport::Glob { prefix } => prefix,
    };
    let mut segments = path.segments.clone();
    loop {
        if let Some(&i) = index.get(&Path {
            segments: segments.clone(),
        }) {
            return Some(i);
        }
        if segments.pop().is_none() {
            return None;
        }
    }
}

fn merge_effective_exports(
    effective: &mut [HashMap<Name, OpDef>],
    target: usize,
    source: usize,
) -> bool {
    let (target_map, source_map) = split_target_source_maps(effective, target, source);
    let mut changed = false;
    for (name, op) in source_map.iter() {
        if merge_into(target_map, name.clone(), op.clone()) {
            changed = true;
        }
    }
    changed
}

fn split_target_source_maps(
    effective: &mut [HashMap<Name, OpDef>],
    target: usize,
    source: usize,
) -> (&mut HashMap<Name, OpDef>, &HashMap<Name, OpDef>) {
    debug_assert_ne!(target, source);
    if target < source {
        let (left, right) = effective.split_at_mut(source);
        (&mut left[target], &right[0])
    } else {
        let (left, right) = effective.split_at_mut(target);
        (&mut right[0], &left[source])
    }
}

/// 実効 export op マップへの取り込み。変化があれば true（不動点の駆動用）。
/// fixity の有無で変化を判定する（rhs を優先して or-merge）。
fn merge_into(map: &mut HashMap<Name, OpDef>, name: Name, op: OpDef) -> bool {
    match map.get_mut(&name) {
        Some(existing) => {
            let before = fixity_shape(existing);
            existing.prefix = op.prefix.or(existing.prefix.take());
            existing.infix = op.infix.or(existing.infix.take());
            existing.suffix = op.suffix.or(existing.suffix.take());
            existing.nullfix = existing.nullfix || op.nullfix;
            before != fixity_shape(existing)
        }
        None => {
            map.insert(name, op);
            true
        }
    }
}

fn fixity_shape(op: &OpDef) -> (bool, bool, bool, bool) {
    (
        op.prefix.is_some(),
        op.infix.is_some(),
        op.suffix.is_some(),
        op.nullfix,
    )
}

/// op テーブルへの挿入（既存と or-merge）。旧 sources の insert_table_op_def 相当。
fn insert_op(table: &mut OpTable, name: Name, op: OpDef) {
    let key = name.0;
    let merged = table
        .0
        .get(key.as_bytes())
        .cloned()
        .map(|existing| merge_op_defs(existing, op.clone()))
        .unwrap_or(op);
    table.0.insert(key.into(), merged);
}

fn merge_op_defs(mut lhs: OpDef, rhs: OpDef) -> OpDef {
    lhs.prefix = rhs.prefix.or(lhs.prefix);
    lhs.infix = rhs.infix.or(lhs.infix);
    lhs.suffix = rhs.suffix.or(lhs.suffix);
    lhs.nullfix = lhs.nullfix || rhs.nullfix;
    lhs
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn reads_leading_uses_and_ops() {
        let source = "use std::prelude::*\nuse a::b as c\ninfix (<+>) 50 50 = foo\nmy main = 1\n";
        let header = read_header(source);

        // use: glob と alias を1つずつ
        assert_eq!(header.uses.len(), 2, "uses: {:?}", header.uses);
        assert!(
            matches!(
                &header.uses[0].import,
                UseImport::Glob { prefix }
                    if prefix.segments == vec![Name("std".into()), Name("prelude".into())]
            ),
            "first use: {:?}",
            header.uses[0]
        );
        assert!(
            matches!(
                &header.uses[1].import,
                UseImport::Alias { name, path }
                    if name == &Name("c".into())
                        && path.segments == vec![Name("a".into()), Name("b".into())]
            ),
            "second use: {:?}",
            header.uses[1]
        );

        // op: <+> を1つ、infix として
        assert_eq!(header.ops.len(), 1, "ops: {:?}", header.ops);
        assert_eq!(header.ops[0].name, Name("<+>".into()));
        assert!(header.ops[0].op.infix.is_some());
    }

    #[test]
    fn read_header_tracks_use_mod_load_directive() {
        let source = "use mod math::*\nmy main = 1\n";
        let header = read_header(source);

        assert_eq!(
            header.module_loads,
            vec![ModuleLoadDirective {
                name: Name("math".into()),
                kind: ModuleLoadKind::UseMod,
                visibility: Visibility::Our,
            }]
        );
        assert!(
            matches!(
                &header.uses[0].import,
                UseImport::Glob { prefix }
                    if prefix.segments == vec![Name("math".into())]
            ),
            "use mod should still behave as a normal use import: {:?}",
            header.uses[0]
        );
    }

    fn path(segments: &[&str]) -> Path {
        Path {
            segments: segments.iter().map(|s| Name(s.to_string())).collect(),
        }
    }

    #[test]
    fn read_header_expands_group_use_imports() {
        let source = "use std::io::{Read, Write}\nmy main = 1\n";
        let header = read_header(source);

        assert_eq!(
            header.uses,
            vec![
                UseDecl {
                    visibility: Visibility::Our,
                    import: UseImport::Alias {
                        name: Name("Read".into()),
                        path: path(&["std", "io", "Read"]),
                    },
                },
                UseDecl {
                    visibility: Visibility::Our,
                    import: UseImport::Alias {
                        name: Name("Write".into()),
                        path: path(&["std", "io", "Write"]),
                    },
                },
            ]
        );
    }

    #[test]
    fn read_header_expands_group_operator_and_alias_imports() {
        let source = "use m::{(+), id, other as o}\nmy main = 1\n";
        let header = read_header(source);

        assert_eq!(
            header.uses,
            vec![
                UseDecl {
                    visibility: Visibility::Our,
                    import: UseImport::Alias {
                        name: Name("+".into()),
                        path: path(&["m", "+"]),
                    },
                },
                UseDecl {
                    visibility: Visibility::Our,
                    import: UseImport::Alias {
                        name: Name("id".into()),
                        path: path(&["m", "id"]),
                    },
                },
                UseDecl {
                    visibility: Visibility::Our,
                    import: UseImport::Alias {
                        name: Name("o".into()),
                        path: path(&["m", "other"]),
                    },
                },
            ]
        );
    }

    fn module_cst(source: &str) -> SyntaxNode<YulangLanguage> {
        SyntaxNode::new_root(parser::parse_module_to_green(source))
    }

    #[test]
    fn module_load_requests_track_external_mod_and_use_mod_only() {
        let root =
            module_cst("mod foo;\nuse mod bar::*\nuse baz::qux\nuse repo/realm/band::module\n");
        let requests = module_load_requests(&path(&["root"]), &root);

        assert_eq!(
            requests,
            vec![
                ModuleLoadRequest {
                    parent: path(&["root"]),
                    name: Name("foo".into()),
                    kind: ModuleLoadKind::ModDecl,
                    visibility: Visibility::Our,
                },
                ModuleLoadRequest {
                    parent: path(&["root"]),
                    name: Name("bar".into()),
                    kind: ModuleLoadKind::UseMod,
                    visibility: Visibility::Our,
                },
            ]
        );
    }

    #[test]
    fn module_load_requests_recurse_into_inline_modules() {
        let root = module_cst("mod outer:\n  pub mod inner;\nmod inline:\n  my x = 1\n");
        let requests = module_load_requests(&path(&["root"]), &root);

        assert_eq!(
            requests,
            vec![ModuleLoadRequest {
                parent: path(&["root", "outer"]),
                name: Name("inner".into()),
                kind: ModuleLoadKind::ModDecl,
                visibility: Visibility::Pub,
            }]
        );
    }

    #[test]
    fn load_attaches_module_load_requests_to_loaded_file() {
        let loaded = load(vec![SourceFile {
            module_path: path(&["root"]),
            source: "mod foo;\nuse mod bar::*\nmy x = 1\n".into(),
        }]);

        assert_eq!(
            loaded[0]
                .module_loads
                .iter()
                .map(ModuleLoadRequest::module_path)
                .collect::<Vec<_>>(),
            vec![path(&["root", "foo"]), path(&["root", "bar"])]
        );
    }

    #[test]
    fn load_with_loaded_prefix_uses_prefix_exports_for_suffix_parse() {
        let prefix = load(vec![SourceFile {
            module_path: path(&["ops"]),
            source: "pub infix (<+>) 50 50 = add\n".into(),
        }]);
        let loaded = load_with_loaded_prefix(
            &prefix,
            vec![SourceFile {
                module_path: Path::default(),
                source: "use ops::*\nmy y = 1 <+> 2\n".into(),
            }],
        );
        let root = loaded
            .iter()
            .find(|file| file.module_path.segments.is_empty())
            .unwrap();
        let root_cst = SyntaxNode::<YulangLanguage>::new_root(root.cst.clone());

        assert_eq!(loaded[0].module_path, path(&["ops"]));
        assert!(root.op_table.0.get("<+>".as_bytes()).is_some());
        assert!(
            root_cst
                .descendants_with_tokens()
                .filter_map(NodeOrToken::into_token)
                .any(|token| token.kind() == SyntaxKind::Infix && token.text() == "<+>")
        );
    }

    #[test]
    fn compiled_syntax_surface_round_trips_operator_exports_for_suffix_parse() {
        let prefix = load(vec![SourceFile {
            module_path: path(&["ops"]),
            source: "pub infix (<+>) 50 50 = add\n".into(),
        }]);
        let surface = CompiledSyntaxSurface::from_loaded_files(&prefix);
        let encoded = serde_json::to_string(&surface).unwrap();
        let decoded: CompiledSyntaxSurface = serde_json::from_str(&encoded).unwrap();
        let loaded = load_suffix_with_syntax_prefix(
            &decoded,
            vec![SourceFile {
                module_path: Path::default(),
                source: "use ops::*\nmy y = 1 <+> 2\n".into(),
            }],
        );
        let root = loaded
            .iter()
            .find(|file| file.module_path.segments.is_empty())
            .unwrap();
        let root_cst = SyntaxNode::<YulangLanguage>::new_root(root.cst.clone());

        assert_eq!(loaded.len(), 1);
        assert!(root.op_table.0.get("<+>".as_bytes()).is_some());
        assert!(
            root_cst
                .descendants_with_tokens()
                .filter_map(NodeOrToken::into_token)
                .any(|token| token.kind() == SyntaxKind::Infix && token.text() == "<+>")
        );
    }

    #[test]
    fn compiled_syntax_surface_does_not_export_my_operator() {
        let prefix = load(vec![SourceFile {
            module_path: path(&["ops"]),
            source: "my infix (<secret>) 50 50 = add\n".into(),
        }]);
        let surface = CompiledSyntaxSurface::from_loaded_files(&prefix);
        let loaded = load_suffix_with_syntax_prefix(
            &surface,
            vec![SourceFile {
                module_path: Path::default(),
                source: "use ops::*\nmy y = 1 <secret> 2\n".into(),
            }],
        );
        let root = loaded
            .iter()
            .find(|file| file.module_path.segments.is_empty())
            .unwrap();

        assert!(surface.files[0].ops.is_empty());
        assert!(root.op_table.0.get("<secret>".as_bytes()).is_none());
    }

    #[test]
    fn compiled_syntax_surface_merge_combines_synthetic_parent_modules() {
        let a = syntax_surface_with_synthetic_root("a", "<a>");
        let b = syntax_surface_with_synthetic_root("b", "<b>");

        let merged = CompiledSyntaxSurface::merge_prefixes([&a, &b]).unwrap();
        let root = merged
            .files
            .iter()
            .find(|file| file.module_path.segments.is_empty())
            .unwrap();
        let loaded = load_suffix_with_syntax_prefix(
            &merged,
            vec![SourceFile {
                module_path: Path::default(),
                source: "use a::*\nuse b::*\nmy x = 1 <a> 2\nmy y = 3 <b> 4\n".into(),
            }],
        );
        let suffix = loaded
            .iter()
            .find(|file| file.module_path.segments.is_empty())
            .unwrap();

        assert_eq!(
            root.module_loads
                .iter()
                .map(ModuleLoadRequest::module_path)
                .collect::<Vec<_>>(),
            vec![path(&["a"]), path(&["b"])]
        );
        assert!(suffix.op_table.0.get("<a>".as_bytes()).is_some());
        assert!(suffix.op_table.0.get("<b>".as_bytes()).is_some());
    }

    #[test]
    fn compiled_syntax_surface_merge_rejects_operator_conflict() {
        let lhs = CompiledSyntaxSurface::from_loaded_files(&load(vec![SourceFile {
            module_path: path(&["ops"]),
            source: "pub infix (<+>) 50 50 = add\n".into(),
        }]));
        let rhs = CompiledSyntaxSurface::from_loaded_files(&load(vec![SourceFile {
            module_path: path(&["ops"]),
            source: "pub infix (<+>) 60 60 = add\n".into(),
        }]));

        let error = CompiledSyntaxSurface::merge_prefixes([&lhs, &rhs]).unwrap_err();

        assert_eq!(
            error,
            CompiledSyntaxMergeError::ConflictingOperator {
                module_path: path(&["ops"]),
                name: Name("<+>".into()),
            }
        );
    }

    #[test]
    fn imported_ops_reach_dependent_file() {
        let files = vec![
            SourceFile {
                module_path: path(&["a"]),
                source: "pub infix (<+>) 50 50 = foo\nmy x = 1\n".into(),
            },
            SourceFile {
                module_path: path(&["b"]),
                source: "use a\nmy y = 1\n".into(),
            },
        ];
        let loaded = load(files);
        assert!(
            loaded[1].op_table.0.get("<+>".as_bytes()).is_some(),
            "b should see a's exported op"
        );
    }

    #[test]
    fn cyclic_use_resolves_ops_both_ways() {
        let files = vec![
            SourceFile {
                module_path: path(&["a"]),
                source: "use b\npub infix (<a>) 50 50 = foo\n".into(),
            },
            SourceFile {
                module_path: path(&["b"]),
                source: "use a\npub infix (<b>) 50 50 = bar\n".into(),
            },
        ];
        let loaded = load(files);
        assert!(
            loaded[0].op_table.0.get("<b>".as_bytes()).is_some(),
            "a should see b's op across the cycle"
        );
        assert!(
            loaded[1].op_table.0.get("<a>".as_bytes()).is_some(),
            "b should see a's op across the cycle"
        );
    }

    fn syntax_surface_with_synthetic_root(module: &str, op: &str) -> CompiledSyntaxSurface {
        let loaded = load(vec![SourceFile {
            module_path: path(&[module]),
            source: format!("pub infix ({op}) 50 50 = add\n"),
        }]);
        let mut surface = CompiledSyntaxSurface::from_loaded_files(&loaded);
        surface.files.push(CompiledSyntaxFile {
            module_path: Path::default(),
            uses: Vec::new(),
            ops: Vec::new(),
            module_loads: vec![ModuleLoadRequest {
                parent: Path::default(),
                name: Name(module.to_string()),
                kind: ModuleLoadKind::ModDecl,
                visibility: Visibility::Our,
            }],
        });
        surface
    }
}
