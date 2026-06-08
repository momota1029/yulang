//! `infer` は、`sources` の CST から `poly` IR と型情報を作るための作業 crate。
//!
//! この crate は最終 IR ではなく、推論中に増える状態を持つ。たとえば constraint machine、
//! use-site 型 table、selection watcher、open SCC graph はここに置く。`poly` 側は最終的に
//! 読まれる構造と解決結果だけを保持する。
//!
//! 現在の入口は pass1: CST を走査してモジュールマップを作る段階。
//! ここでは DefId 採番と名前空間登録だけを行い、body lowering や型制約には踏み込まない。
//! pass2 で、式 lower・名前解決・weighted subtype constraint seed・selection/SCC event routing を
//! 同じ作業 arena の上へ載せる。

pub mod analysis;
pub mod arena;
pub mod constraints;
pub mod scc;
pub mod typing;
pub mod uses;

pub use arena::Arena;

use std::collections::HashMap;

use poly::expr::{Arena as PolyArena, Def, DefId, Vis};
use rowan::SyntaxNode;
use sources::{Name, UseImport};
use yulang_parser::lex::SyntaxKind;
use yulang_parser::sink::YulangLanguage;

type Cst = SyntaxNode<YulangLanguage>;

// ── モジュールツリー（infer 作業用。名前解決が済めば poly には残さない）──────

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
/// pass1 / pass2 の作業用 module ID。
///
/// `poly` の最終 IR へは残さない。名前解決中に「今どの module scope にいるか」を持つための
/// infer-local な ID。
pub struct ModuleId(usize);

struct ModuleNode {
    /// 親モジュール。pass2 のスコープ外探索（上→下）で使う予定。
    #[allow(dead_code)]
    parent: Option<ModuleId>,
    values: HashMap<Name, DefId>,
    modules: HashMap<Name, ModuleId>,
    /// この場で宣言された use（エイリアス）。解決は pass2 で「集めながら」行う。
    aliases: Vec<(UseImport, Vis)>,
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
                values: HashMap::new(),
                modules: HashMap::new(),
                aliases: Vec::new(),
            }],
        }
    }
    pub fn root_id(&self) -> ModuleId {
        ModuleId(0)
    }
    fn new_module(&mut self, parent: ModuleId) -> ModuleId {
        let id = ModuleId(self.nodes.len());
        self.nodes.push(ModuleNode {
            parent: Some(parent),
            values: HashMap::new(),
            modules: HashMap::new(),
            aliases: Vec::new(),
        });
        id
    }
    fn insert_value(&mut self, module: ModuleId, name: Name, def: DefId) {
        self.nodes[module.0].values.insert(name, def);
    }
    fn insert_module(&mut self, module: ModuleId, name: Name, sub: ModuleId) {
        self.nodes[module.0].modules.insert(name, sub);
    }
    fn add_alias(&mut self, module: ModuleId, import: UseImport, vis: Vis) {
        self.nodes[module.0].aliases.push((import, vis));
    }
    pub fn aliases(&self, module: ModuleId) -> &[(UseImport, Vis)] {
        &self.nodes[module.0].aliases
    }
    pub fn value(&self, module: ModuleId, name: &Name) -> Option<DefId> {
        self.nodes[module.0].values.get(name).copied()
    }
    pub fn module(&self, module: ModuleId, name: &Name) -> Option<ModuleId> {
        self.nodes[module.0].modules.get(name).copied()
    }
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
                        self.modules.insert_value(module, name, def);
                        children.push(def);
                    }
                }
                SyntaxKind::ModDecl => {
                    if let Some(name) = mod_name(&child) {
                        let vis = vis_of(&child);
                        // 先に DefId を採番してから子を登録し、最後に完成版を set する。
                        let def = self.arena.defs.fresh();
                        let sub = self.modules.new_module(module);
                        let sub_children = self.register_mod_body(&child, sub);
                        self.arena.defs.set(
                            def,
                            Def::Mod {
                                vis,
                                children: sub_children,
                            },
                        );
                        self.modules.insert_module(module, name, sub);
                        children.push(def);
                    }
                }
                SyntaxKind::UseDecl => {
                    let vis = vis_of(&child);
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
}

/// pass1 の入口。フルパース済み CST のモジュールマップを作る。
pub fn lower_module_map(root: &Cst) -> Lower {
    let mut lower = Lower::new();
    let root_module = lower.modules.root_id();
    let roots = lower.register_block(root, root_module);
    lower.arena.roots = roots;
    lower
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
        assert!(lower.modules.value(root, &Name("f".into())).is_some());
        assert!(lower.modules.value(root, &Name("g".into())).is_some());
        assert_eq!(lower.arena.roots.len(), 2);
    }

    #[test]
    fn collects_use_aliases() {
        let cst = parse("use a::b as c\nuse x::y::*\nmy f = 1\n");
        let lower = lower_module_map(&cst);
        let root = lower.modules.root_id();
        // alias c と glob x::y の 2 本が溜まる（解決は pass2）
        assert_eq!(lower.modules.aliases(root).len(), 2);
        assert!(lower.modules.value(root, &Name("f".into())).is_some());
    }

    #[test]
    fn registers_nested_module() {
        let cst = parse("mod m:\n  my x = 1\n");
        let lower = lower_module_map(&cst);
        let root = lower.modules.root_id();
        let m = lower
            .modules
            .module(root, &Name("m".into()))
            .expect("module m registered");
        assert!(lower.modules.value(m, &Name("x".into())).is_some());
    }
}
