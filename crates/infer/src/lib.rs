//! `infer` は、`sources` の CST から `poly` IR と型情報を作るための作業 crate。
//!
//! この crate は最終 IR ではなく、推論中に増える状態を持つ。たとえば constraint machine、
//! use-site 型 table、selection watcher、open SCC graph はここに置く。`poly` 側は最終的に
//! 読まれる構造と解決結果だけを保持する。
//!
//! 現在の入口は pass1: CST を走査してモジュールマップを作る段階と、pass2 first cut:
//! binding body を `ExprLowerer` で lower して `Def::Let.body` と `DefId` 型 slot を埋める段階。
//! 型定義系、import view、lambda / pattern local scope はまだこの足場へ接続していない。

pub mod analysis;
pub mod arena;
pub mod constraints;
pub mod dump;
pub mod lowering;
pub mod patterns;
pub mod scc;
pub mod typing;
pub mod uses;

pub use arena::Arena;

use poly::dump::DumpLabels;
use poly::expr::{Arena as PolyArena, Def, DefId, Vis};
use rowan::SyntaxNode;
use rustc_hash::FxHashMap;
use sources::{LoadedFile, Name, Path as ModulePath, UseImport};
use std::fmt;
use yulang_parser::lex::SyntaxKind;
use yulang_parser::sink::YulangLanguage;

type Cst = SyntaxNode<YulangLanguage>;

// ── モジュールツリー（infer 作業用。名前解決が済めば poly には残さない）──────

/// pass1 / pass2 の作業用 module ID。
///
/// `poly` の最終 IR へは残さない。名前解決中に「今どの module scope にいるか」を持つための
/// infer-local な ID。
#[derive(Clone, Copy, PartialEq, Eq, Debug, Hash)]
pub struct ModuleId(usize);

/// module 内の宣言位置。
///
/// 同じ module の中で、宣言が source 上のどの順に現れたかを表す。
/// resolver はこの order を基準に「上に同名宣言があれば最後、なければ下の直近」を選ぶ。
/// binding body は header の後を解決しているので、同じ order の宣言も既に見えているものとして扱う。
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Debug, Hash)]
pub struct ModuleOrder(u32);

impl ModuleOrder {
    pub fn from_index(index: u32) -> Self {
        Self(index)
    }

    pub fn index(self) -> u32 {
        self.0
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
struct ModuleParent {
    module: ModuleId,
    order: ModuleOrder,
}

struct ModuleNode {
    /// 親モジュールと、親の宣言列におけるこの module 宣言の order。
    parent: Option<ModuleParent>,
    decls: Vec<ModuleDecl>,
    values: FxHashMap<Name, Vec<ModuleDeclId>>,
    modules: FxHashMap<Name, Vec<ModuleDeclId>>,
    /// この場で宣言された use（エイリアス）。解決は pass2 で不動点を回して import view にする。
    aliases: Vec<AliasDecl>,
    next_order: u32,
}

#[derive(Clone, Copy, PartialEq, Eq, Debug, Hash)]
struct ModuleDeclId(usize);

#[derive(Debug, Clone)]
struct ModuleDecl {
    name: Name,
    vis: Vis,
    order: ModuleOrder,
    kind: ModuleDeclKind,
}

/// module 内の値宣言を外へ見せるための summary。
///
/// resolver 本体は `value_at` を使うが、import view や diagnostics は宣言名・visibility・order も
/// 必要になるため、`DefId` だけを返す API に閉じない。
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ModuleValueDecl {
    pub name: Name,
    pub vis: Vis,
    pub order: ModuleOrder,
    pub def: DefId,
}

/// module 内の子 module 宣言を外へ見せるための summary。
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ModuleChildDecl {
    pub name: Name,
    pub vis: Vis,
    pub order: ModuleOrder,
    pub module: ModuleId,
    pub def: DefId,
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(crate) struct ModulePathTarget {
    pub module: ModuleId,
    pub def: Option<DefId>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum ModuleDeclKind {
    Value { def: DefId },
    Module { module: ModuleId, def: DefId },
}

/// module 内の `use` 宣言。
///
/// alias も source order を持つ。今は import view 構築前なので lookup には使わないが、
/// Rust 風の不動点 import 解決へ進む時に、どの地点にある use かを失わないために残す。
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AliasDecl {
    pub import: UseImport,
    pub vis: Vis,
    pub order: ModuleOrder,
}

/// pass1 が作る module scope table。
///
/// 値名・子 module 名・use alias を module ごとに保持する。これは名前解決のための作業 table で、
/// `poly::Arena` には残さない。名前解決が済んだら、必要な結果は `RefId -> DefId` や
/// `SelectId -> SelectResolution` として `poly` に書き戻す。
pub struct ModuleTable {
    nodes: Vec<ModuleNode>,
}

impl ModuleTable {
    fn new() -> Self {
        Self {
            nodes: vec![ModuleNode {
                parent: None,
                decls: Vec::new(),
                values: FxHashMap::default(),
                modules: FxHashMap::default(),
                aliases: Vec::new(),
                next_order: 0,
            }],
        }
    }
    pub fn root_id(&self) -> ModuleId {
        ModuleId(0)
    }
    fn new_module(&mut self) -> ModuleId {
        let id = ModuleId(self.nodes.len());
        self.nodes.push(ModuleNode {
            parent: None,
            decls: Vec::new(),
            values: FxHashMap::default(),
            modules: FxHashMap::default(),
            aliases: Vec::new(),
            next_order: 0,
        });
        id
    }
    fn insert_value(&mut self, module: ModuleId, name: Name, def: DefId, vis: Vis) {
        let decl = self.push_decl(module, name.clone(), vis, ModuleDeclKind::Value { def });
        self.nodes[module.0]
            .values
            .entry(name)
            .or_default()
            .push(decl);
    }
    fn insert_module(&mut self, module: ModuleId, name: Name, sub: ModuleId, def: DefId, vis: Vis) {
        let decl = self.push_decl(
            module,
            name.clone(),
            vis,
            ModuleDeclKind::Module { module: sub, def },
        );
        let order = self.nodes[module.0].decls[decl.0].order;
        self.nodes[module.0]
            .modules
            .entry(name)
            .or_default()
            .push(decl);
        self.nodes[sub.0].parent = Some(ModuleParent { module, order });
    }
    fn add_alias(&mut self, module: ModuleId, import: UseImport, vis: Vis) {
        let order = self.next_order(module);
        self.nodes[module.0]
            .aliases
            .push(AliasDecl { import, vis, order });
    }
    pub fn aliases(&self, module: ModuleId) -> &[AliasDecl] {
        &self.nodes[module.0].aliases
    }
    pub fn value_at(&self, module: ModuleId, name: &Name, site: ModuleOrder) -> Option<DefId> {
        let decl = self.select_decl(module, self.nodes[module.0].values.get(name)?, site)?;
        match decl.kind {
            ModuleDeclKind::Value { def } => Some(def),
            ModuleDeclKind::Module { .. } => None,
        }
    }
    pub fn module_at(&self, module: ModuleId, name: &Name, site: ModuleOrder) -> Option<ModuleId> {
        let decl = self.select_decl(module, self.nodes[module.0].modules.get(name)?, site)?;
        match decl.kind {
            ModuleDeclKind::Module { module, .. } => Some(module),
            ModuleDeclKind::Value { .. } => None,
        }
    }
    pub fn lexical_value_at(
        &self,
        mut module: ModuleId,
        name: &Name,
        mut site: ModuleOrder,
    ) -> Option<DefId> {
        loop {
            if let Some(def) = self.value_at(module, name, site) {
                return Some(def);
            }
            let parent = self.nodes[module.0].parent?;
            module = parent.module;
            site = parent.order;
        }
    }
    pub fn lexical_module_at(
        &self,
        mut module: ModuleId,
        name: &Name,
        mut site: ModuleOrder,
    ) -> Option<ModuleId> {
        loop {
            if let Some(found) = self.module_at(module, name, site) {
                return Some(found);
            }
            let parent = self.nodes[module.0].parent?;
            module = parent.module;
            site = parent.order;
        }
    }
    pub fn module_by_path(&self, path: &ModulePath) -> Option<ModuleId> {
        let mut module = self.root_id();
        for segment in &path.segments {
            module = self.first_module_decl(module, segment)?.module;
        }
        Some(module)
    }
    pub fn value_decls(&self, module: ModuleId, name: &Name) -> Vec<ModuleValueDecl> {
        self.nodes[module.0]
            .values
            .get(name)
            .into_iter()
            .flat_map(|decls| decls.iter())
            .filter_map(|decl| {
                let decl = &self.nodes[module.0].decls[decl.0];
                match decl.kind {
                    ModuleDeclKind::Value { def } => Some(ModuleValueDecl {
                        name: decl.name.clone(),
                        vis: decl.vis,
                        order: decl.order,
                        def,
                    }),
                    ModuleDeclKind::Module { .. } => None,
                }
            })
            .collect()
    }
    pub fn module_decls(&self, module: ModuleId, name: &Name) -> Vec<ModuleChildDecl> {
        self.nodes[module.0]
            .modules
            .get(name)
            .into_iter()
            .flat_map(|decls| decls.iter())
            .filter_map(|decl| {
                let decl = &self.nodes[module.0].decls[decl.0];
                match decl.kind {
                    ModuleDeclKind::Module { module, def } => Some(ModuleChildDecl {
                        name: decl.name.clone(),
                        vis: decl.vis,
                        order: decl.order,
                        module,
                        def,
                    }),
                    ModuleDeclKind::Value { .. } => None,
                }
            })
            .collect()
    }
    fn first_module_decl(&self, module: ModuleId, name: &Name) -> Option<ModuleChildDecl> {
        self.module_decls(module, name).into_iter().next()
    }
    /// dump 用の source label table を作る。
    ///
    /// `poly` は source 名を本体に持たないため、名前を読める dump が必要な時だけ
    /// infer-local の module table から `DefId -> source path` を投影する。
    pub fn dump_labels(&self) -> DumpLabels {
        let mut labels = DumpLabels::new();
        self.add_dump_labels(self.root_id(), &mut Vec::new(), &mut labels);
        labels
    }
    fn push_decl(
        &mut self,
        module: ModuleId,
        name: Name,
        vis: Vis,
        kind: ModuleDeclKind,
    ) -> ModuleDeclId {
        let order = self.next_order(module);
        let node = &mut self.nodes[module.0];
        let id = ModuleDeclId(node.decls.len());
        node.decls.push(ModuleDecl {
            name,
            vis,
            order,
            kind,
        });
        id
    }
    fn next_order(&mut self, module: ModuleId) -> ModuleOrder {
        let node = &mut self.nodes[module.0];
        let order = ModuleOrder(node.next_order);
        node.next_order += 1;
        order
    }
    fn select_decl(
        &self,
        module: ModuleId,
        decls: &[ModuleDeclId],
        site: ModuleOrder,
    ) -> Option<&ModuleDecl> {
        let node = &self.nodes[module.0];
        decls
            .iter()
            .map(|decl| &node.decls[decl.0])
            .filter(|decl| decl.order <= site)
            .max_by_key(|decl| decl.order)
            .or_else(|| {
                decls
                    .iter()
                    .map(|decl| &node.decls[decl.0])
                    .filter(|decl| decl.order > site)
                    .min_by_key(|decl| decl.order)
            })
    }
    fn add_dump_labels(&self, module: ModuleId, prefix: &mut Vec<String>, labels: &mut DumpLabels) {
        for decl in &self.nodes[module.0].decls {
            let label = qualified_label(prefix, &decl.name);
            match decl.kind {
                ModuleDeclKind::Value { def } => {
                    labels.set_def_label(def, label);
                }
                ModuleDeclKind::Module { module, def } => {
                    labels.set_def_label(def, label);
                    prefix.push(decl.name.0.clone());
                    self.add_dump_labels(module, prefix, labels);
                    prefix.pop();
                }
            }
        }
    }
}

fn qualified_label(prefix: &[String], name: &Name) -> String {
    if prefix.is_empty() {
        return name.0.clone();
    }

    let mut label = prefix.join(".");
    label.push('.');
    label.push_str(&name.0);
    label
}

// ── pass1 ────────────────────────────────────────────────────────────────

/// pass1 の出力。
///
/// `arena` は DefId と module children を含む薄い `poly` IR、`modules` は pass2 で scope を引くための
/// infer-local table。body と型制約はまだ空のまま残す。
pub struct Lower {
    /// pass1 が採番した `poly` Arena。
    pub arena: PolyArena,
    /// pass2 の名前解決で使う infer-local module map。
    pub modules: ModuleTable,
}

impl Lower {
    fn new() -> Self {
        Self {
            arena: PolyArena::new(),
            modules: ModuleTable::new(),
        }
    }

    /// ブロック（root / IndentBlock / BraceGroup）の直下を走査して定義を採番する。
    /// 採番した DefId の並びを返す（呼び出し側が roots / Mod.children に入れる）。
    fn register_block(&mut self, block: &Cst, module: ModuleId) -> Vec<DefId> {
        let mut children = Vec::new();
        for child in block.children() {
            match child.kind() {
                SyntaxKind::Binding => {
                    if let Some(name) = binding_name(&child) {
                        let vis = binding_vis(&child);
                        let def = self.arena.defs.fresh();
                        self.arena.defs.set(
                            def,
                            Def::Let {
                                vis,
                                scheme: None,
                                body: None,
                                children: Vec::new(),
                            },
                        );
                        self.modules.insert_value(module, name, def, vis);
                        children.push(def);
                    }
                }
                SyntaxKind::ModDecl => {
                    if let Some(name) = mod_name(&child) {
                        let vis = vis_of(&child);
                        let (def, sub, created) = self.ensure_child_module(module, name, vis);
                        let sub_children = self.register_mod_body(&child, sub);
                        self.set_module_children(def, sub_children);
                        if created {
                            children.push(def);
                        }
                    }
                }
                SyntaxKind::UseDecl => {
                    let vis = vis_of(&child);
                    if let Some(name) = use_mod_name(&child) {
                        let (def, _, created) = self.ensure_child_module(module, name, vis);
                        if created {
                            children.push(def);
                        }
                    }
                    for import in sources::use_imports(&child) {
                        self.modules.add_alias(module, import, vis);
                    }
                }
                // 型定義系（Type/Struct/Enum/Role/Impl/Act/Cast/Error）・OpDef は後で。
                _ => {}
            }
        }
        children
    }

    /// ModDecl の body（BraceGroup / IndentBlock）に降りて定義を採番する。
    /// 外部 mod（Semicolon）や body 無しでは空を返す。
    fn register_mod_body(&mut self, mod_decl: &Cst, sub: ModuleId) -> Vec<DefId> {
        for child in mod_decl.children() {
            if matches!(
                child.kind(),
                SyntaxKind::BraceGroup | SyntaxKind::IndentBlock
            ) {
                return self.register_block(&child, sub);
            }
        }
        Vec::new()
    }

    fn ensure_child_module(
        &mut self,
        module: ModuleId,
        name: Name,
        vis: Vis,
    ) -> (DefId, ModuleId, bool) {
        if let Some(existing) = self.modules.first_module_decl(module, &name) {
            return (existing.def, existing.module, false);
        }

        let def = self.arena.defs.fresh();
        let sub = self.modules.new_module();
        self.arena.defs.set(
            def,
            Def::Mod {
                vis,
                children: Vec::new(),
            },
        );
        self.modules.insert_module(module, name, sub, def, vis);
        (def, sub, true)
    }

    fn set_module_children(&mut self, def: DefId, children: Vec<DefId>) {
        let Some(Def::Mod { children: slot, .. }) = self.arena.defs.get_mut(def) else {
            return;
        };
        *slot = children;
    }

    pub(crate) fn module_path_target(&self, path: &ModulePath) -> Option<ModulePathTarget> {
        let mut target = ModulePathTarget {
            module: self.modules.root_id(),
            def: None,
        };
        for segment in &path.segments {
            let decl = self.modules.first_module_decl(target.module, segment)?;
            target = ModulePathTarget {
                module: decl.module,
                def: Some(decl.def),
            };
        }
        Some(target)
    }
}

/// pass1 の入口。フルパース済み CST のモジュールマップを作る。
pub fn lower_module_map(root: &Cst) -> Lower {
    let mut lower = Lower::new();
    let root_module = lower.modules.root_id();
    let roots = lower.register_block(root, root_module);
    lower.arena.roots = roots;
    lower
}

/// 複数 `LoadedFile` から1つの module map を作る。
///
/// root file を先に登録し、`mod foo;` / `use mod foo::*` が作った module skeleton に
/// child file の block を差し込む。file path 解決や op table 確定は `sources` 側の責務。
pub fn lower_loaded_files_module_map(files: &[LoadedFile]) -> Result<Lower, LoadedFilesError> {
    let loaded = LoadedFileCsts::new(files)?;
    lower_loaded_file_csts_module_map(&loaded)
}

pub(crate) fn lower_loaded_file_csts_module_map(
    loaded: &LoadedFileCsts,
) -> Result<Lower, LoadedFilesError> {
    let mut lower = Lower::new();

    let root = loaded.root().ok_or(LoadedFilesError::MissingRoot)?;
    let roots = lower.register_block(&root.cst, lower.modules.root_id());
    lower.arena.roots = roots;

    for file in loaded.non_root_by_depth() {
        let Some(target) = lower.module_path_target(&file.module_path) else {
            return Err(LoadedFilesError::MissingModulePath {
                module_path: file.module_path.clone(),
            });
        };
        let Some(def) = target.def else {
            continue;
        };
        let children = lower.register_block(&file.cst, target.module);
        lower.set_module_children(def, children);
    }

    Ok(lower)
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum LoadedFilesError {
    MissingRoot,
    DuplicateModulePath { module_path: ModulePath },
    MissingModulePath { module_path: ModulePath },
}

impl fmt::Display for LoadedFilesError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::MissingRoot => write!(f, "loaded files do not contain a root module"),
            Self::DuplicateModulePath { module_path } => write!(
                f,
                "loaded files contain duplicate module `{}`",
                format_module_path(module_path)
            ),
            Self::MissingModulePath { module_path } => write!(
                f,
                "loaded module `{}` has no module declaration in its parent",
                format_module_path(module_path)
            ),
        }
    }
}

impl std::error::Error for LoadedFilesError {}

pub(crate) struct LoadedFileCsts {
    files: Vec<LoadedFileCst>,
}

pub(crate) struct LoadedFileCst {
    pub module_path: ModulePath,
    pub cst: Cst,
}

impl LoadedFileCsts {
    pub(crate) fn new(files: &[LoadedFile]) -> Result<Self, LoadedFilesError> {
        let mut seen = FxHashMap::default();
        let mut indexed = Vec::with_capacity(files.len());
        for file in files {
            if seen.insert(file.module_path.clone(), ()).is_some() {
                return Err(LoadedFilesError::DuplicateModulePath {
                    module_path: file.module_path.clone(),
                });
            }
            indexed.push(LoadedFileCst {
                module_path: file.module_path.clone(),
                cst: SyntaxNode::<YulangLanguage>::new_root(file.cst.clone()),
            });
        }
        indexed.sort_by_key(|file| {
            (
                file.module_path.segments.len(),
                module_path_sort_key(&file.module_path),
            )
        });
        Ok(Self { files: indexed })
    }

    pub(crate) fn root(&self) -> Option<&LoadedFileCst> {
        self.files
            .iter()
            .find(|file| file.module_path.segments.is_empty())
    }

    pub(crate) fn by_depth(&self) -> impl Iterator<Item = &LoadedFileCst> {
        self.files.iter()
    }

    fn non_root_by_depth(&self) -> impl Iterator<Item = &LoadedFileCst> {
        self.files
            .iter()
            .filter(|file| !file.module_path.segments.is_empty())
    }
}

fn module_path_sort_key(path: &ModulePath) -> String {
    path.segments
        .iter()
        .map(|name| name.0.as_str())
        .collect::<Vec<_>>()
        .join("\0")
}

fn format_module_path(path: &ModulePath) -> String {
    if path.segments.is_empty() {
        return "<root>".to_string();
    }
    path.segments
        .iter()
        .map(|name| name.0.as_str())
        .collect::<Vec<_>>()
        .join("::")
}

// ── CST ヘルパ ───────────────────────────────────────────────────────────

fn child_node(node: &Cst, kind: SyntaxKind) -> Option<Cst> {
    node.children().find(|c| c.kind() == kind)
}

fn first_ident(node: &Cst) -> Option<Name> {
    node.children_with_tokens()
        .filter_map(|it| it.into_token())
        .find(|t| t.kind() == SyntaxKind::Ident)
        .map(|t| Name(t.text().to_string()))
}

/// `Binding → BindingHeader → Pattern` の最初の Ident が束縛名。
/// （`my (a, b) = …` のような分解束縛は後で対応。今は最初の Ident を返す）
fn binding_name(node: &Cst) -> Option<Name> {
    let header = child_node(node, SyntaxKind::BindingHeader)?;
    let pattern = child_node(&header, SyntaxKind::Pattern)?;
    first_ident(&pattern)
}

fn binding_vis(node: &Cst) -> Vis {
    match child_node(node, SyntaxKind::BindingHeader) {
        Some(header) => vis_of(&header),
        None => Vis::Our,
    }
}

/// ModDecl の最初の Ident がモジュール名。
fn mod_name(node: &Cst) -> Option<Name> {
    first_ident(node)
}

/// `use mod foo::...` の `foo`。
///
/// parser の設計では `use mod path` は `mod path_head; use path` の sugar なので、
/// pass1 でも先頭 module を module skeleton として登録する。
fn use_mod_name(node: &Cst) -> Option<Name> {
    let mut after_mod = false;
    for item in node.children_with_tokens() {
        let Some(token) = item.into_token() else {
            continue;
        };
        match token.kind() {
            SyntaxKind::Mod => after_mod = true,
            SyntaxKind::Ident if after_mod => return Some(Name(token.text().to_string())),
            _ => {}
        }
    }
    None
}

/// 直下の My/Our/Pub トークンを読む。無ければ Our（省略時の既定）。
fn vis_of(node: &Cst) -> Vis {
    node.children_with_tokens()
        .filter_map(|it| it.into_token())
        .find_map(|t| match t.kind() {
            SyntaxKind::Pub => Some(Vis::Pub),
            SyntaxKind::Our => Some(Vis::Our),
            SyntaxKind::My => Some(Vis::My),
            _ => None,
        })
        .unwrap_or(Vis::Our)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn parse(src: &str) -> Cst {
        SyntaxNode::new_root(yulang_parser::parse_module_to_green(src))
    }

    #[test]
    fn registers_top_level_bindings() {
        let cst = parse("my f = 1\npub g = 2\n");
        let lower = lower_module_map(&cst);
        let root = lower.modules.root_id();
        let f = lower.modules.value_decls(root, &Name("f".into()));
        let g = lower.modules.value_decls(root, &Name("g".into()));
        assert_eq!(f.len(), 1);
        assert_eq!(g.len(), 1);
        assert_eq!(lower.arena.roots.len(), 2);
    }

    #[test]
    fn collects_use_aliases() {
        let cst = parse("use a::b as c\nuse x::y::*\nmy f = 1\n");
        let lower = lower_module_map(&cst);
        let root = lower.modules.root_id();
        // alias c と glob x::y の 2 本が溜まる（解決は pass2）
        assert_eq!(lower.modules.aliases(root).len(), 2);
        assert_eq!(lower.modules.value_decls(root, &Name("f".into())).len(), 1);
    }

    #[test]
    fn registers_nested_module() {
        let cst = parse("mod m:\n  my x = 1\n");
        let lower = lower_module_map(&cst);
        let root = lower.modules.root_id();
        let module_decls = lower.modules.module_decls(root, &Name("m".into()));
        let [m_decl] = module_decls.as_slice() else {
            panic!("module m should be registered once");
        };
        assert_eq!(m_decl.order, ModuleOrder(0));
        let m = m_decl.module;
        assert_eq!(lower.modules.value_decls(m, &Name("x".into())).len(), 1);
    }

    #[test]
    fn ordered_lookup_prefers_last_previous_decl() {
        let cst = parse("my a = 1\nmy b = a\nmy a = 2\n");
        let lower = lower_module_map(&cst);
        let root = lower.modules.root_id();
        let a_decls = lower.modules.value_decls(root, &Name("a".into()));
        let b_order = lower.modules.value_decls(root, &Name("b".into()))[0].order;

        assert_eq!(a_decls.len(), 2);
        assert_eq!(
            lower.modules.value_at(root, &Name("a".into()), b_order),
            Some(a_decls[0].def)
        );
    }

    #[test]
    fn ordered_lookup_uses_nearest_following_decl_when_no_previous_decl_exists() {
        let cst = parse("my b = a\nmy a = 1\nmy a = 2\n");
        let lower = lower_module_map(&cst);
        let root = lower.modules.root_id();
        let a_decls = lower.modules.value_decls(root, &Name("a".into()));
        let b_order = lower.modules.value_decls(root, &Name("b".into()))[0].order;

        assert_eq!(
            lower.modules.value_at(root, &Name("a".into()), b_order),
            Some(a_decls[0].def)
        );
    }

    #[test]
    fn lexical_lookup_converts_child_site_to_parent_module_order() {
        let cst = parse("mod m:\n  my y = x\nmy x = 1\n");
        let lower = lower_module_map(&cst);
        let root = lower.modules.root_id();
        let m = lower.modules.module_decls(root, &Name("m".into()))[0].module;
        let y_order = lower.modules.value_decls(m, &Name("y".into()))[0].order;
        let x = lower.modules.value_decls(root, &Name("x".into()))[0].def;

        assert_eq!(
            lower
                .modules
                .lexical_value_at(m, &Name("x".into()), y_order),
            Some(x)
        );
    }

    #[test]
    fn lexical_lookup_prefers_parent_decl_before_child_module_over_later_parent_decl() {
        let cst = parse("my x = 0\nmod m:\n  my y = x\nmy x = 1\n");
        let lower = lower_module_map(&cst);
        let root = lower.modules.root_id();
        let m = lower.modules.module_decls(root, &Name("m".into()))[0].module;
        let y_order = lower.modules.value_decls(m, &Name("y".into()))[0].order;
        let x_decls = lower.modules.value_decls(root, &Name("x".into()));

        assert_eq!(
            lower
                .modules
                .lexical_value_at(m, &Name("x".into()), y_order),
            Some(x_decls[0].def)
        );
    }
}
