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

#[derive(Debug, Clone, Default, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct Path {
    pub segments: Vec<Name>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Visibility {
    Pub,
    Our,
    My,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum UseImport {
    /// `use a::b::c` / `use a::b as c`
    Alias { name: Name, path: Path },
    /// `use a::b::*`
    Glob { prefix: Path },
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct UseDecl {
    pub visibility: Visibility,
    pub import: UseImport,
}

/// 外部 module ファイルを読むきっかけになる構文。
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
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
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ModuleLoadDirective {
    pub name: Name,
    pub kind: ModuleLoadKind,
}

/// 外部 module ファイルを読む要求。
///
/// `parent` はこの要求が現れた inline module の path、`name` はその直下に生える子 module 名。
/// たとえば root module 内の `mod foo;` は `parent = []`, `name = foo`。
/// `mod outer: mod inner;` は `parent = [outer]`, `name = inner`。
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ModuleLoadRequest {
    pub parent: Path,
    pub name: Name,
    pub kind: ModuleLoadKind,
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

// ── 複数ファイルの読み込み ──────────────────────────────────────────────
// 依存解決 → 実効 export op の不動点 → ファイル別初期テーブル → フルパース。
// 全段階が順序無関係（先読み独立／不動点収束／フルパース独立）＝SCC は不要。

/// 入力ファイル。`module_path` は収集層（FS を辿る上位層）が付けてくる前提。
pub struct SourceFile {
    pub module_path: Path,
    pub source: String,
}

/// 先読み・op テーブル確定・フルパースまで済んだファイル。
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
    let n = files.len();

    // 1. 先読み（各ファイル独立）
    let headers: Vec<Header> = files.iter().map(|f| read_header(&f.source)).collect();

    // 2. module_path → ファイル index
    let mut index: HashMap<Path, usize> = HashMap::with_capacity(n);
    for (i, f) in files.iter().enumerate() {
        index.insert(f.module_path.clone(), i);
    }

    // 3. 自前 export op（先頭の pub/our op。my はファイル内のみ）
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

    // 4. pub/our use の再エクスポート連鎖を不動点で閉包（循環でも単調収束）
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
                for (name, op) in effective[j].clone() {
                    if merge_into(&mut effective[i], name, op) {
                        changed = true;
                    }
                }
            }
        }
        if !changed {
            break;
        }
    }

    // 5+6. 各ファイルの初期テーブル（standard + use 先の実効 export op）でフルパース。
    //      自前 op はフルパース中に update_op_table が順次入れるので、ここでは入れない。
    let mut loaded = Vec::with_capacity(n);
    for (i, (file, header)) in files.into_iter().zip(headers).enumerate() {
        let mut table = standard_op_table();
        for use_decl in &header.uses {
            if let Some(j) = resolve_use(&use_decl.import, &index) {
                if j == i {
                    continue;
                }
                for (name, op) in &effective[j] {
                    insert_op(&mut table, name.clone(), op.clone());
                }
            }
        }
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
                },
                ModuleLoadRequest {
                    parent: path(&["root"]),
                    name: Name("bar".into()),
                    kind: ModuleLoadKind::UseMod,
                },
            ]
        );
    }

    #[test]
    fn module_load_requests_recurse_into_inline_modules() {
        let root = module_cst("mod outer:\n  mod inner;\nmod inline:\n  my x = 1\n");
        let requests = module_load_requests(&path(&["root"]), &root);

        assert_eq!(
            requests,
            vec![ModuleLoadRequest {
                parent: path(&["root", "outer"]),
                name: Name("inner".into()),
                kind: ModuleLoadKind::ModDecl,
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
}
