//! `infer` は、`sources` の CST から `poly` IR と型情報を作るための作業 crate。
//!
//! この crate は最終 IR ではなく、推論中に増える状態を持つ。たとえば constraint machine、
//! use-site 型 table、selection watcher、open SCC graph はここに置く。`poly` 側は最終的に
//! 読まれる構造と解決結果だけを保持する。
//!
//! 現在の入口は pass1: CST を走査してモジュールマップを作る段階と、pass2 first cut:
//! binding body を `ExprLowerer` で lower して `Def::Let.body` と `DefId` 型 slot を埋める段階。
//! 型定義系の本体 lowering はまだこの足場へ接続していない。

pub mod analysis;
pub mod annotation;
pub mod arena;
pub mod casts;
pub mod compact;
pub mod constraints;
pub mod dump;
pub mod generalize;
pub mod instantiate;
pub mod lowering;
pub mod methods;
pub mod patterns;
mod role_solve;
pub mod roles;
pub mod scc;
pub mod typing;
pub mod uses;

pub use arena::Arena;

use poly::dump::DumpLabels;
use poly::expr::{Arena as PolyArena, Def, DefId, Vis};
use rowan::{NodeOrToken, SyntaxNode};
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
    types: FxHashMap<Name, Vec<ModuleDeclId>>,
    modules: FxHashMap<Name, Vec<ModuleDeclId>>,
    /// この場で宣言された use（エイリアス）。解決は pass2 で不動点を回して import view にする。
    aliases: Vec<AliasDecl>,
    import_values: FxHashMap<Name, Vec<ImportedValueDecl>>,
    import_types: FxHashMap<Name, Vec<ImportedTypeDecl>>,
    import_modules: FxHashMap<Name, Vec<ImportedModuleDecl>>,
    next_order: u32,
}

#[derive(Clone, Copy, PartialEq, Eq, Debug, Hash)]
struct ModuleDeclId(usize);

#[derive(Clone, Copy, PartialEq, Eq, Debug, Hash)]
/// 型名前空間の宣言 identity。
///
/// `poly::DefId` は値・module の IR node を指すため、型名だけの first cut では infer-local な
/// ID を使う。型宣言本体を lower する段階で、必要なら別の永続 identity へ写す。
pub struct TypeDeclId(u32);

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

/// module 内の型宣言を外へ見せるための summary。
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ModuleTypeDecl {
    pub name: Name,
    pub vis: Vis,
    pub order: ModuleOrder,
    pub module: ModuleId,
    pub id: TypeDeclId,
    pub kind: ModuleTypeKind,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ActOperationDecl {
    pub effect: ModuleTypeDecl,
    pub name: Name,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TypeMethodDecl {
    pub owner: TypeDeclId,
    pub name: Name,
    pub receiver: Name,
    pub receiver_kind: TypeMethodReceiver,
    pub def: DefId,
    pub vis: Vis,
    pub order: ModuleOrder,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ActMethodDecl {
    pub owner: TypeDeclId,
    pub name: Name,
    pub receiver: Name,
    pub def: DefId,
    pub vis: Vis,
    pub order: ModuleOrder,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RoleMethodDecl {
    pub owner: TypeDeclId,
    pub name: Name,
    pub receiver: Option<Name>,
    pub def: DefId,
    pub vis: Vis,
    pub order: ModuleOrder,
    pub signature: Option<SyntaxNode<YulangLanguage>>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RoleImplDecl {
    pub def: DefId,
    pub module: ModuleId,
    pub body_module: ModuleId,
    pub order: ModuleOrder,
    pub methods: Vec<RoleImplMethodDecl>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RoleImplMethodDecl {
    pub name: Name,
    pub receiver: Option<Name>,
    pub def: DefId,
    pub vis: Vis,
    pub order: ModuleOrder,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TypeMethodReceiver {
    Value,
    Ref,
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
/// 型名前空間に登録される宣言の種類。
pub enum ModuleTypeKind {
    TypeAlias,
    Struct,
    Enum,
    Error,
    Role,
    Act,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum ModuleDeclKind {
    Value {
        def: DefId,
    },
    Type {
        id: TypeDeclId,
        kind: ModuleTypeKind,
    },
    Module {
        module: ModuleId,
        def: DefId,
    },
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

#[derive(Debug, Clone, PartialEq, Eq)]
struct ImportedValueDecl {
    order: ModuleOrder,
    def: DefId,
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct ImportedTypeDecl {
    order: ModuleOrder,
    decl: ModuleTypeDecl,
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct ImportedModuleDecl {
    order: ModuleOrder,
    module: ModuleId,
}

struct ImportPathTarget {
    value: Option<DefId>,
    ty: Option<ModuleTypeDecl>,
    module: Option<ModuleId>,
}

/// pass1 が作る module scope table。
///
/// 値名・子 module 名・use alias を module ごとに保持する。これは名前解決のための作業 table で、
/// `poly::Arena` には残さない。名前解決が済んだら、必要な結果は `RefId -> DefId` や
/// `SelectId -> SelectResolution` として `poly` に書き戻す。
pub struct ModuleTable {
    nodes: Vec<ModuleNode>,
    act_ops: FxHashMap<TypeDeclId, Vec<Name>>,
    act_methods: FxHashMap<TypeDeclId, Vec<ActMethodDecl>>,
    role_inputs: FxHashMap<TypeDeclId, Vec<String>>,
    role_associated: FxHashMap<TypeDeclId, Vec<String>>,
    role_impls: FxHashMap<ModuleId, Vec<RoleImplDecl>>,
    role_methods: FxHashMap<TypeDeclId, Vec<RoleMethodDecl>>,
    type_companions: FxHashMap<TypeDeclId, ModuleId>,
    type_methods: FxHashMap<TypeDeclId, Vec<TypeMethodDecl>>,
    next_type_id: u32,
}

impl ModuleTable {
    fn new() -> Self {
        Self {
            nodes: vec![ModuleNode {
                parent: None,
                decls: Vec::new(),
                values: FxHashMap::default(),
                types: FxHashMap::default(),
                modules: FxHashMap::default(),
                aliases: Vec::new(),
                import_values: FxHashMap::default(),
                import_types: FxHashMap::default(),
                import_modules: FxHashMap::default(),
                next_order: 0,
            }],
            act_ops: FxHashMap::default(),
            act_methods: FxHashMap::default(),
            role_inputs: FxHashMap::default(),
            role_associated: FxHashMap::default(),
            role_impls: FxHashMap::default(),
            role_methods: FxHashMap::default(),
            type_companions: FxHashMap::default(),
            type_methods: FxHashMap::default(),
            next_type_id: 0,
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
            types: FxHashMap::default(),
            modules: FxHashMap::default(),
            aliases: Vec::new(),
            import_values: FxHashMap::default(),
            import_types: FxHashMap::default(),
            import_modules: FxHashMap::default(),
            next_order: 0,
        });
        id
    }
    fn new_anonymous_child_module(&mut self, parent: ModuleId, order: ModuleOrder) -> ModuleId {
        let module = self.new_module();
        self.nodes[module.0].parent = Some(ModuleParent {
            module: parent,
            order,
        });
        module
    }
    fn insert_value(&mut self, module: ModuleId, name: Name, def: DefId, vis: Vis) -> ModuleOrder {
        let decl = self.push_decl(module, name.clone(), vis, ModuleDeclKind::Value { def });
        let order = self.nodes[module.0].decls[decl.0].order;
        self.nodes[module.0]
            .values
            .entry(name)
            .or_default()
            .push(decl);
        order
    }
    fn insert_type(
        &mut self,
        module: ModuleId,
        name: Name,
        kind: ModuleTypeKind,
        vis: Vis,
    ) -> TypeDeclId {
        let id = self.next_type_decl_id();
        let decl = self.push_decl(module, name.clone(), vis, ModuleDeclKind::Type { id, kind });
        self.nodes[module.0]
            .types
            .entry(name)
            .or_default()
            .push(decl);
        id
    }
    fn set_act_ops(&mut self, id: TypeDeclId, ops: Vec<Name>) {
        self.act_ops.insert(id, ops);
    }
    fn insert_act_method(&mut self, method: ActMethodDecl) {
        self.act_methods
            .entry(method.owner)
            .or_default()
            .push(method);
    }
    pub fn act_methods(&self, id: TypeDeclId) -> &[ActMethodDecl] {
        self.act_methods.get(&id).map(Vec::as_slice).unwrap_or(&[])
    }
    pub fn all_act_methods(&self) -> impl Iterator<Item = &ActMethodDecl> {
        self.act_methods.values().flat_map(|methods| methods.iter())
    }
    fn set_role_inputs(&mut self, id: TypeDeclId, inputs: Vec<String>) {
        self.role_inputs.insert(id, inputs);
    }
    pub fn role_inputs(&self, id: TypeDeclId) -> &[String] {
        self.role_inputs.get(&id).map(Vec::as_slice).unwrap_or(&[])
    }
    fn set_role_associated(&mut self, id: TypeDeclId, associated: Vec<String>) {
        self.role_associated.insert(id, associated);
    }
    pub fn role_associated(&self, id: TypeDeclId) -> &[String] {
        self.role_associated
            .get(&id)
            .map(Vec::as_slice)
            .unwrap_or(&[])
    }
    fn insert_role_impl(&mut self, impl_decl: RoleImplDecl) {
        self.role_impls
            .entry(impl_decl.module)
            .or_default()
            .push(impl_decl);
    }
    pub fn role_impls(&self, module: ModuleId) -> &[RoleImplDecl] {
        self.role_impls
            .get(&module)
            .map(Vec::as_slice)
            .unwrap_or(&[])
    }
    fn insert_role_method(&mut self, method: RoleMethodDecl) {
        self.role_methods
            .entry(method.owner)
            .or_default()
            .push(method);
    }
    pub fn role_methods(&self, id: TypeDeclId) -> &[RoleMethodDecl] {
        self.role_methods.get(&id).map(Vec::as_slice).unwrap_or(&[])
    }
    pub fn all_role_methods(&self) -> impl Iterator<Item = &RoleMethodDecl> {
        self.role_methods
            .values()
            .flat_map(|methods| methods.iter())
    }
    fn set_type_companion(&mut self, id: TypeDeclId, module: ModuleId) {
        self.type_companions.insert(id, module);
    }
    pub fn type_companion(&self, id: TypeDeclId) -> Option<ModuleId> {
        self.type_companions.get(&id).copied()
    }
    fn insert_type_method(&mut self, method: TypeMethodDecl) {
        self.type_methods
            .entry(method.owner)
            .or_default()
            .push(method);
    }
    pub fn type_methods(&self, id: TypeDeclId) -> &[TypeMethodDecl] {
        self.type_methods.get(&id).map(Vec::as_slice).unwrap_or(&[])
    }
    pub fn all_type_methods(&self) -> impl Iterator<Item = &TypeMethodDecl> {
        self.type_methods
            .values()
            .flat_map(|methods| methods.iter())
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
    fn build_import_views(&mut self) {
        for module_index in 0..self.nodes.len() {
            let module = ModuleId(module_index);
            let aliases = self.nodes[module_index].aliases.clone();
            for alias in aliases {
                self.import_alias(module, &alias);
            }
        }
    }
    pub fn value_at(&self, module: ModuleId, name: &Name, site: ModuleOrder) -> Option<DefId> {
        let decl = self.select_decl(module, self.nodes[module.0].values.get(name)?, site)?;
        match decl.kind {
            ModuleDeclKind::Value { def } => Some(def),
            ModuleDeclKind::Type { .. } | ModuleDeclKind::Module { .. } => None,
        }
    }
    pub fn type_at(
        &self,
        module: ModuleId,
        name: &Name,
        site: ModuleOrder,
    ) -> Option<ModuleTypeDecl> {
        let decl = self.select_decl(module, self.nodes[module.0].types.get(name)?, site)?;
        match decl.kind {
            ModuleDeclKind::Type { id, kind } => Some(ModuleTypeDecl {
                name: decl.name.clone(),
                vis: decl.vis,
                order: decl.order,
                module,
                id,
                kind,
            }),
            ModuleDeclKind::Value { .. } | ModuleDeclKind::Module { .. } => None,
        }
    }
    pub fn module_at(&self, module: ModuleId, name: &Name, site: ModuleOrder) -> Option<ModuleId> {
        let decl = self.select_decl(module, self.nodes[module.0].modules.get(name)?, site)?;
        match decl.kind {
            ModuleDeclKind::Module { module, .. } => Some(module),
            ModuleDeclKind::Value { .. } | ModuleDeclKind::Type { .. } => None,
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
            if let Some(def) = self.imported_value_at(module, name, site) {
                return Some(def);
            }
            let parent = self.nodes[module.0].parent?;
            module = parent.module;
            site = parent.order;
        }
    }
    pub fn value_path_at(
        &self,
        module: ModuleId,
        path: &[Name],
        site: ModuleOrder,
    ) -> Option<DefId> {
        let Some((last, prefix)) = path.split_last() else {
            return None;
        };
        if prefix.is_empty() {
            return self.lexical_value_at(module, last, site);
        }

        let target = self.raw_module_path_from(module, prefix, site)?;
        self.value_at(target, last, module_path_site())
    }
    pub fn type_path_at(
        &self,
        module: ModuleId,
        path: &[Name],
        site: ModuleOrder,
    ) -> Option<ModuleTypeDecl> {
        let Some((last, prefix)) = path.split_last() else {
            return None;
        };
        if prefix.is_empty() {
            return self.lexical_type_at(module, last, site);
        }

        let target = self.raw_module_path_from(module, prefix, site)?;
        self.type_at(target, last, module_path_site())
    }
    pub fn act_operation_decls_at(
        &self,
        module: ModuleId,
        effect_path: &[Name],
        site: ModuleOrder,
    ) -> Vec<ActOperationDecl> {
        let Some(effect) = self
            .type_path_at(module, effect_path, site)
            .filter(|decl| decl.kind == ModuleTypeKind::Act)
        else {
            return Vec::new();
        };

        self.act_ops
            .get(&effect.id)
            .into_iter()
            .flat_map(|ops| ops.iter())
            .cloned()
            .map(|name| ActOperationDecl {
                effect: effect.clone(),
                name,
            })
            .collect()
    }
    pub fn lexical_type_at(
        &self,
        mut module: ModuleId,
        name: &Name,
        mut site: ModuleOrder,
    ) -> Option<ModuleTypeDecl> {
        loop {
            if let Some(found) = self.type_at(module, name, site) {
                return Some(found);
            }
            if let Some(found) = self.imported_type_at(module, name, site) {
                return Some(found);
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
            if let Some(found) = self.imported_module_at(module, name, site) {
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
    pub fn module_path(&self, mut module: ModuleId) -> ModulePath {
        let mut segments = Vec::new();
        while let Some(parent) = self.nodes[module.0].parent {
            let parent_node = &self.nodes[parent.module.0];
            let Some(decl) = parent_node.decls.iter().find(|decl| {
                decl.order == parent.order
                    && matches!(
                        decl.kind,
                        ModuleDeclKind::Module { module: child, .. } if child == module
                    )
            }) else {
                break;
            };
            segments.push(decl.name.clone());
            module = parent.module;
        }
        segments.reverse();
        ModulePath { segments }
    }
    pub fn type_decl_path(&self, decl: &ModuleTypeDecl) -> ModulePath {
        let mut path = self.module_path(decl.module);
        path.segments.push(decl.name.clone());
        path
    }
    pub fn type_decl_by_id(&self, id: TypeDeclId) -> Option<ModuleTypeDecl> {
        for module_index in 0..self.nodes.len() {
            let module = ModuleId(module_index);
            for decl in &self.nodes[module_index].decls {
                if let ModuleDeclKind::Type { id: decl_id, kind } = decl.kind
                    && decl_id == id
                {
                    return Some(ModuleTypeDecl {
                        name: decl.name.clone(),
                        vis: decl.vis,
                        order: decl.order,
                        module,
                        id: decl_id,
                        kind,
                    });
                }
            }
        }
        None
    }
    fn import_alias(&mut self, module: ModuleId, alias: &AliasDecl) {
        match &alias.import {
            UseImport::Alias { name, path } => {
                let Some(target) = self.import_path_target(module, path, alias.order) else {
                    return;
                };
                if let Some(def) = target.value {
                    self.nodes[module.0]
                        .import_values
                        .entry(name.clone())
                        .or_default()
                        .push(ImportedValueDecl {
                            order: alias.order,
                            def,
                        });
                }
                if let Some(decl) = target.ty {
                    self.nodes[module.0]
                        .import_types
                        .entry(name.clone())
                        .or_default()
                        .push(ImportedTypeDecl {
                            order: alias.order,
                            decl,
                        });
                }
                if let Some(found) = target.module {
                    self.nodes[module.0]
                        .import_modules
                        .entry(name.clone())
                        .or_default()
                        .push(ImportedModuleDecl {
                            order: alias.order,
                            module: found,
                        });
                }
            }
            UseImport::Glob { prefix } => {
                let Some(target) = self.raw_module_path_from(module, &prefix.segments, alias.order)
                else {
                    return;
                };
                for decl in self.module_value_imports(target) {
                    self.nodes[module.0]
                        .import_values
                        .entry(decl.name.clone())
                        .or_default()
                        .push(ImportedValueDecl {
                            order: alias.order,
                            def: decl.def,
                        });
                }
                for decl in self.module_type_imports(target) {
                    self.nodes[module.0]
                        .import_types
                        .entry(decl.name.clone())
                        .or_default()
                        .push(ImportedTypeDecl {
                            order: alias.order,
                            decl,
                        });
                }
                for decl in self.module_module_imports(target) {
                    self.nodes[module.0]
                        .import_modules
                        .entry(decl.name.clone())
                        .or_default()
                        .push(ImportedModuleDecl {
                            order: alias.order,
                            module: decl.module,
                        });
                }
            }
        }
    }
    fn import_path_target(
        &self,
        module: ModuleId,
        path: &ModulePath,
        site: ModuleOrder,
    ) -> Option<ImportPathTarget> {
        let Some((last, prefix)) = path.segments.split_last() else {
            return None;
        };
        if prefix.is_empty() {
            return Some(ImportPathTarget {
                value: self.raw_lexical_value_at(module, last, site),
                ty: self.raw_lexical_type_at(module, last, site),
                module: self.raw_lexical_module_at(module, last, site),
            });
        }

        let target = self.raw_module_path_from(module, prefix, site)?;
        Some(ImportPathTarget {
            value: self.value_at(target, last, module_path_site()),
            ty: self.type_at(target, last, module_path_site()),
            module: self.module_at(target, last, module_path_site()),
        })
    }
    fn raw_module_path_from(
        &self,
        module: ModuleId,
        path: &[Name],
        site: ModuleOrder,
    ) -> Option<ModuleId> {
        let Some((first, rest)) = path.split_first() else {
            return Some(module);
        };
        let mut current = self.raw_lexical_module_at(module, first, site)?;
        for segment in rest {
            current = self.module_at(current, segment, module_path_site())?;
        }
        Some(current)
    }
    fn raw_lexical_value_at(
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
    fn raw_lexical_type_at(
        &self,
        mut module: ModuleId,
        name: &Name,
        mut site: ModuleOrder,
    ) -> Option<ModuleTypeDecl> {
        loop {
            if let Some(found) = self.type_at(module, name, site) {
                return Some(found);
            }
            let parent = self.nodes[module.0].parent?;
            module = parent.module;
            site = parent.order;
        }
    }
    fn raw_lexical_module_at(
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
    fn imported_value_at(&self, module: ModuleId, name: &Name, site: ModuleOrder) -> Option<DefId> {
        self.select_import(self.nodes[module.0].import_values.get(name)?, site)
            .map(|decl| decl.def)
    }
    fn imported_type_at(
        &self,
        module: ModuleId,
        name: &Name,
        site: ModuleOrder,
    ) -> Option<ModuleTypeDecl> {
        self.select_import(self.nodes[module.0].import_types.get(name)?, site)
            .map(|decl| decl.decl.clone())
    }
    fn imported_module_at(
        &self,
        module: ModuleId,
        name: &Name,
        site: ModuleOrder,
    ) -> Option<ModuleId> {
        self.select_import(self.nodes[module.0].import_modules.get(name)?, site)
            .map(|decl| decl.module)
    }
    fn module_value_imports(&self, module: ModuleId) -> Vec<ModuleValueDecl> {
        self.nodes[module.0]
            .values
            .keys()
            .flat_map(|name| self.value_decls(module, name))
            .collect()
    }
    fn module_type_imports(&self, module: ModuleId) -> Vec<ModuleTypeDecl> {
        self.nodes[module.0]
            .types
            .keys()
            .flat_map(|name| self.type_decls(module, name))
            .collect()
    }
    fn module_module_imports(&self, module: ModuleId) -> Vec<ModuleChildDecl> {
        self.nodes[module.0]
            .modules
            .keys()
            .flat_map(|name| self.module_decls(module, name))
            .collect()
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
                    ModuleDeclKind::Type { .. } | ModuleDeclKind::Module { .. } => None,
                }
            })
            .collect()
    }
    pub fn type_decls(&self, module: ModuleId, name: &Name) -> Vec<ModuleTypeDecl> {
        self.nodes[module.0]
            .types
            .get(name)
            .into_iter()
            .flat_map(|decls| decls.iter())
            .filter_map(|decl| {
                let decl = &self.nodes[module.0].decls[decl.0];
                match decl.kind {
                    ModuleDeclKind::Type { id, kind } => Some(ModuleTypeDecl {
                        name: decl.name.clone(),
                        vis: decl.vis,
                        order: decl.order,
                        module,
                        id,
                        kind,
                    }),
                    ModuleDeclKind::Value { .. } | ModuleDeclKind::Module { .. } => None,
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
                    ModuleDeclKind::Value { .. } | ModuleDeclKind::Type { .. } => None,
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
    fn next_type_decl_id(&mut self) -> TypeDeclId {
        let id = TypeDeclId(self.next_type_id);
        self.next_type_id += 1;
        id
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
    fn select_import<'a, T>(&self, imports: &'a [T], site: ModuleOrder) -> Option<&'a T>
    where
        T: ImportOrder,
    {
        imports
            .iter()
            .filter(|decl| decl.order() <= site)
            .max_by_key(|decl| decl.order())
            .or_else(|| {
                imports
                    .iter()
                    .filter(|decl| decl.order() > site)
                    .min_by_key(|decl| decl.order())
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
                ModuleDeclKind::Type { .. } => {}
            }
        }
    }
}

trait ImportOrder {
    fn order(&self) -> ModuleOrder;
}

impl ImportOrder for ImportedValueDecl {
    fn order(&self) -> ModuleOrder {
        self.order
    }
}

impl ImportOrder for ImportedTypeDecl {
    fn order(&self) -> ModuleOrder {
        self.order
    }
}

impl ImportOrder for ImportedModuleDecl {
    fn order(&self) -> ModuleOrder {
        self.order
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
                SyntaxKind::TypeDecl
                | SyntaxKind::StructDecl
                | SyntaxKind::EnumDecl
                | SyntaxKind::ErrorDecl
                | SyntaxKind::RoleDecl
                | SyntaxKind::ActDecl => {
                    self.register_type_namespace_decl(&child, module, &mut children);
                }
                // 型定義系の本体、Cast/OpDef は後で。
                SyntaxKind::ImplDecl => {
                    if let Some(def) = self.register_role_impl_decl(&child, module) {
                        children.push(def);
                    }
                }
                _ => {}
            }
        }
        children
    }

    fn register_role_impl_decl(&mut self, node: &Cst, module: ModuleId) -> Option<DefId> {
        let order = self.modules.next_order(module);
        let def = self.arena.defs.fresh();
        self.arena.defs.set(
            def,
            Def::Mod {
                vis: Vis::My,
                children: Vec::new(),
            },
        );
        let body_module = self.modules.new_anonymous_child_module(module, order);
        let (children, methods) = role_impl_body(node)
            .map(|body| self.register_role_impl_block(&body, body_module))
            .unwrap_or_default();
        self.set_module_children(def, children);
        self.modules.insert_role_impl(RoleImplDecl {
            def,
            module,
            body_module,
            order,
            methods,
        });
        Some(def)
    }

    fn register_role_impl_block(
        &mut self,
        block: &Cst,
        module: ModuleId,
    ) -> (Vec<DefId>, Vec<RoleImplMethodDecl>) {
        let mut children = Vec::new();
        let mut methods = Vec::new();
        for child in block.children() {
            match child.kind() {
                SyntaxKind::Binding => {
                    if let Some(method) = role_method_binding(&child) {
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
                        let order =
                            self.modules
                                .insert_value(module, method.name.clone(), def, vis);
                        children.push(def);
                        if vis != Vis::My {
                            methods.push(RoleImplMethodDecl {
                                name: method.name,
                                receiver: method.receiver,
                                def,
                                vis,
                                order,
                            });
                        }
                    } else if let Some(name) = binding_name(&child) {
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
                        self.append_module_children(def, sub_children);
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
                SyntaxKind::TypeDecl
                | SyntaxKind::StructDecl
                | SyntaxKind::EnumDecl
                | SyntaxKind::ErrorDecl
                | SyntaxKind::RoleDecl
                | SyntaxKind::ActDecl => {
                    self.register_type_namespace_decl(&child, module, &mut children);
                }
                _ => {}
            }
        }
        (children, methods)
    }

    fn register_type_namespace_decl(
        &mut self,
        node: &Cst,
        module: ModuleId,
        children: &mut Vec<DefId>,
    ) {
        let (Some(name), Some(kind)) = (type_decl_name(node), module_type_kind(node.kind())) else {
            return;
        };
        let vis = vis_of(node);
        let id = self.modules.insert_type(module, name.clone(), kind, vis);
        if kind == ModuleTypeKind::Act {
            self.modules.set_act_ops(id, act_operation_names(node));
            self.register_act_companion(node, module, name.clone(), id, vis, children);
        }
        if kind == ModuleTypeKind::Role {
            self.modules.set_role_inputs(id, role_input_names(node));
            self.modules
                .set_role_associated(id, role_associated_names(node));
            self.register_role_companion(node, module, name.clone(), id, vis, children);
        }
        if matches!(
            kind,
            ModuleTypeKind::TypeAlias
                | ModuleTypeKind::Struct
                | ModuleTypeKind::Enum
                | ModuleTypeKind::Error
        ) {
            self.register_type_constructors(node, module, kind, name.clone(), vis, children);
            self.register_type_companion(node, module, name, id, vis, children);
        }
    }

    fn register_type_constructors(
        &mut self,
        node: &Cst,
        module: ModuleId,
        kind: ModuleTypeKind,
        name: Name,
        vis: Vis,
        children: &mut Vec<DefId>,
    ) {
        match kind {
            ModuleTypeKind::TypeAlias if type_self_struct_node(node).is_some() => {
                let def = self.register_synthetic_value(module, name, vis);
                children.push(def);
            }
            ModuleTypeKind::Struct => {
                let def = self.register_synthetic_value(module, name, vis);
                children.push(def);
            }
            ModuleTypeKind::Enum | ModuleTypeKind::Error => {
                for variant in enum_variant_nodes(node) {
                    let Some(name) = enum_variant_name(&variant) else {
                        continue;
                    };
                    let def = self.register_synthetic_value(module, name, vis);
                    children.push(def);
                }
            }
            ModuleTypeKind::TypeAlias | ModuleTypeKind::Role | ModuleTypeKind::Act => {}
        }
    }

    fn register_synthetic_value(&mut self, module: ModuleId, name: Name, vis: Vis) -> DefId {
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
        def
    }

    fn register_role_companion(
        &mut self,
        node: &Cst,
        module: ModuleId,
        name: Name,
        owner: TypeDeclId,
        vis: Vis,
        children: &mut Vec<DefId>,
    ) {
        let Some(body) = role_decl_body(node) else {
            return;
        };
        let (def, companion, created) = self.ensure_child_module(module, name, vis);
        self.modules.set_type_companion(owner, companion);
        let companion_children = self.register_role_companion_block(&body, companion, owner);
        self.append_module_children(def, companion_children);
        if created {
            children.push(def);
        }
    }

    fn register_role_companion_block(
        &mut self,
        block: &Cst,
        module: ModuleId,
        owner: TypeDeclId,
    ) -> Vec<DefId> {
        let mut children = Vec::new();
        for child in block.children() {
            match child.kind() {
                SyntaxKind::Binding => {
                    if let Some(method) = role_method_binding(&child) {
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
                        let order =
                            self.modules
                                .insert_value(module, method.name.clone(), def, vis);
                        self.modules.insert_role_method(RoleMethodDecl {
                            owner,
                            name: method.name,
                            receiver: method.receiver,
                            def,
                            vis,
                            order,
                            signature: binding_type_expr(&child),
                        });
                        children.push(def);
                    } else if let Some(name) = binding_name(&child) {
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
                        self.append_module_children(def, sub_children);
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
                SyntaxKind::TypeDecl => {}
                _ => {}
            }
        }
        children
    }

    fn register_act_companion(
        &mut self,
        node: &Cst,
        module: ModuleId,
        name: Name,
        owner: TypeDeclId,
        vis: Vis,
        children: &mut Vec<DefId>,
    ) {
        let Some(body) = act_decl_body(node) else {
            return;
        };
        let (def, companion, created) = self.ensure_child_module(module, name, vis);
        self.modules.set_type_companion(owner, companion);
        let companion_children = self.register_act_companion_block(&body, companion, owner);
        self.append_module_children(def, companion_children);
        if created {
            children.push(def);
        }
    }

    fn register_act_companion_block(
        &mut self,
        block: &Cst,
        module: ModuleId,
        owner: TypeDeclId,
    ) -> Vec<DefId> {
        let mut children = Vec::new();
        for child in block.children() {
            match child.kind() {
                SyntaxKind::Binding if act_operation_binding(&child) => {}
                SyntaxKind::Binding if type_method_binding(&child).is_some() => {
                    let Some(method) = type_method_binding(&child) else {
                        continue;
                    };
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
                    let value_name = act_method_value_name(&method.name, def);
                    let order = self.modules.insert_value(module, value_name, def, vis);
                    self.modules.insert_act_method(ActMethodDecl {
                        owner,
                        name: method.name,
                        receiver: method.receiver,
                        def,
                        vis,
                        order,
                    });
                    children.push(def);
                }
                SyntaxKind::Binding => {
                    let Some(name) = binding_name(&child) else {
                        continue;
                    };
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
                SyntaxKind::ModDecl => {
                    if let Some(name) = mod_name(&child) {
                        let (def, sub, created) =
                            self.ensure_child_module(module, name, vis_of(&child));
                        let sub_children = self.register_mod_body(&child, sub);
                        self.set_module_children(def, sub_children);
                        if created {
                            children.push(def);
                        }
                    }
                }
                _ => {}
            }
        }
        children
    }

    fn register_type_companion(
        &mut self,
        node: &Cst,
        module: ModuleId,
        name: Name,
        owner: TypeDeclId,
        vis: Vis,
        children: &mut Vec<DefId>,
    ) {
        let Some(body) = type_with_body(node) else {
            return;
        };
        let (def, companion, created) = self.ensure_child_module(module, name, vis);
        self.modules.set_type_companion(owner, companion);
        let companion_children = self.register_type_companion_block(&body, companion, owner);
        self.append_module_children(def, companion_children);
        if created {
            children.push(def);
        }
    }

    fn register_type_companion_block(
        &mut self,
        block: &Cst,
        module: ModuleId,
        owner: TypeDeclId,
    ) -> Vec<DefId> {
        let mut children = Vec::new();
        for child in block.children() {
            match child.kind() {
                SyntaxKind::Binding => {
                    if let Some(method) = type_method_binding(&child) {
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
                        let value_name = type_method_value_name(&method.name, method.receiver_kind);
                        let order = self.modules.insert_value(module, value_name, def, vis);
                        self.modules.insert_type_method(TypeMethodDecl {
                            owner,
                            name: method.name,
                            receiver: method.receiver,
                            receiver_kind: method.receiver_kind,
                            def,
                            vis,
                            order,
                        });
                        children.push(def);
                    } else if let Some(name) = binding_name(&child) {
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
                        self.append_module_children(def, sub_children);
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
                SyntaxKind::StructDecl
                    if type_decl_name(&child).is_some_and(|name| name.0 == "self") => {}
                SyntaxKind::TypeDecl
                | SyntaxKind::StructDecl
                | SyntaxKind::EnumDecl
                | SyntaxKind::ErrorDecl
                | SyntaxKind::RoleDecl
                | SyntaxKind::ActDecl => {
                    self.register_type_namespace_decl(&child, module, &mut children);
                }
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

    fn append_module_children(&mut self, def: DefId, children: Vec<DefId>) {
        let Some(Def::Mod { children: slot, .. }) = self.arena.defs.get_mut(def) else {
            return;
        };
        slot.extend(children);
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
    lower.modules.build_import_views();
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

    lower.modules.build_import_views();
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

fn module_path_site() -> ModuleOrder {
    ModuleOrder::from_index(u32::MAX)
}

// ── CST ヘルパ ───────────────────────────────────────────────────────────

fn child_node(node: &Cst, kind: SyntaxKind) -> Option<Cst> {
    node.children().find(|c| c.kind() == kind)
}

fn contains_node_kind(node: &Cst, kind: SyntaxKind) -> bool {
    node.children().any(|child| {
        child.kind() == kind
            || matches!(
                child.kind(),
                SyntaxKind::BindingHeader
                    | SyntaxKind::Pattern
                    | SyntaxKind::TypeAnn
                    | SyntaxKind::TypeExpr
                    | SyntaxKind::TypeApply
                    | SyntaxKind::TypeArrow
                    | SyntaxKind::TypeEffectRow
            ) && contains_node_kind(&child, kind)
    })
}

fn first_ident(node: &Cst) -> Option<Name> {
    node.children_with_tokens()
        .filter_map(|it| it.into_token())
        .find(|t| t.kind() == SyntaxKind::Ident)
        .map(|t| Name(t.text().to_string()))
}

fn first_ident_or_sigil(node: &Cst) -> Option<Name> {
    node.children_with_tokens()
        .filter_map(|it| it.into_token())
        .find(|t| matches!(t.kind(), SyntaxKind::Ident | SyntaxKind::SigilIdent))
        .map(|t| Name(t.text().to_string()))
}

/// `Binding → BindingHeader → Pattern` の最初の Ident が束縛名。
/// （`my (a, b) = …` のような分解束縛は後で対応。今は最初の Ident を返す）
fn binding_name(node: &Cst) -> Option<Name> {
    let header = child_node(node, SyntaxKind::BindingHeader)?;
    let pattern = child_node(&header, SyntaxKind::Pattern)?;
    first_ident_or_sigil(&pattern)
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

/// 型名前空間に登録する宣言名。
pub(crate) fn type_decl_name(node: &Cst) -> Option<Name> {
    if node.kind() == SyntaxKind::RoleDecl {
        return child_node(node, SyntaxKind::TypeExpr)
            .and_then(|type_expr| first_ident(&type_expr));
    }
    first_ident(node)
}

#[derive(Debug, Clone)]
pub(crate) struct TypeMethodBindingInfo {
    pub(crate) name: Name,
    pub(crate) receiver: Name,
    pub(crate) receiver_kind: TypeMethodReceiver,
}

#[derive(Debug, Clone)]
pub(crate) struct RoleMethodBindingInfo {
    pub(crate) name: Name,
    pub(crate) receiver: Option<Name>,
}

pub(crate) fn type_method_binding(node: &Cst) -> Option<TypeMethodBindingInfo> {
    let header = child_node(node, SyntaxKind::BindingHeader)?;
    let pattern = child_node(&header, SyntaxKind::Pattern)?;
    let method = pattern_field_name(&pattern)?;
    let receiver = first_ident_or_sigil(&pattern)?;
    let receiver_kind = if receiver.0.starts_with('&') {
        TypeMethodReceiver::Ref
    } else {
        TypeMethodReceiver::Value
    };
    Some(TypeMethodBindingInfo {
        name: method,
        receiver,
        receiver_kind,
    })
}

pub(crate) fn role_method_binding(node: &Cst) -> Option<RoleMethodBindingInfo> {
    let header = child_node(node, SyntaxKind::BindingHeader)?;
    let pattern = child_node(&header, SyntaxKind::Pattern)?;
    let annotated = contains_node_kind(&pattern, SyntaxKind::TypeAnn);
    let receiver = first_ident_or_sigil(&pattern);
    let method = pattern_field_name(&pattern);
    match (method, receiver, annotated) {
        (Some(method), receiver, _) => Some(RoleMethodBindingInfo {
            name: method,
            receiver,
        }),
        (None, Some(name), true) => Some(RoleMethodBindingInfo {
            name,
            receiver: None,
        }),
        _ => None,
    }
}

pub(crate) fn binding_type_expr(binding: &Cst) -> Option<Cst> {
    let header = child_node(binding, SyntaxKind::BindingHeader)?;
    let pattern = child_node(&header, SyntaxKind::Pattern)?;
    direct_pattern_type_expr(&pattern)
}

pub(crate) fn direct_pattern_type_expr(pattern: &Cst) -> Option<Cst> {
    pattern
        .children()
        .find(|child| child.kind() == SyntaxKind::TypeAnn)
        .and_then(|ann| {
            ann.children()
                .find(|child| child.kind() == SyntaxKind::TypeExpr)
        })
}

fn pattern_field_name(pattern: &Cst) -> Option<Name> {
    pattern
        .children()
        .find(|child| child.kind() == SyntaxKind::Field)?
        .children_with_tokens()
        .filter_map(|item| item.into_token())
        .find(|token| token.kind() == SyntaxKind::DotField)
        .map(|token| Name(token.text().trim_start_matches('.').to_string()))
}

fn type_method_value_name(name: &Name, receiver: TypeMethodReceiver) -> Name {
    match receiver {
        TypeMethodReceiver::Value => name.clone(),
        TypeMethodReceiver::Ref => Name(format!("{}!", name.0)),
    }
}

fn act_method_value_name(name: &Name, def: DefId) -> Name {
    Name(format!("#act-method:{}:{}", name.0, def.0))
}

pub(crate) fn type_var_names(node: &Cst) -> Vec<String> {
    let Some(vars) = child_node(node, SyntaxKind::TypeVars) else {
        return Vec::new();
    };
    let mut out = Vec::new();
    for token in vars
        .children_with_tokens()
        .filter_map(|item| item.into_token())
    {
        if !matches!(token.kind(), SyntaxKind::Ident | SyntaxKind::SigilIdent) {
            continue;
        }
        let name = token.text().trim_start_matches('\'').to_string();
        if !out.contains(&name) {
            out.push(name);
        }
    }
    out
}

pub(crate) fn struct_field_nodes(node: &Cst) -> Vec<Cst> {
    let mut out = Vec::new();
    collect_pre_with_descendants(node, SyntaxKind::StructField, &mut out);
    out
}

pub(crate) fn struct_field_name(node: &Cst) -> Option<Name> {
    node.children_with_tokens()
        .filter_map(|item| item.into_token())
        .find(|token| token.kind() == SyntaxKind::Ident)
        .map(|token| Name(token.text().to_string()))
}

pub(crate) fn field_type_expr(node: &Cst) -> Option<Cst> {
    node.children()
        .find(|child| child.kind() == SyntaxKind::TypeExpr)
}

pub(crate) fn enum_variant_nodes(node: &Cst) -> Vec<Cst> {
    let mut out = Vec::new();
    collect_pre_with_descendants(node, SyntaxKind::EnumVariant, &mut out);
    out
}

pub(crate) fn enum_variant_name(node: &Cst) -> Option<Name> {
    node.children_with_tokens()
        .filter_map(|item| item.into_token())
        .find(|token| token.kind() == SyntaxKind::Ident)
        .map(|token| Name(token.text().to_string()))
}

pub(crate) fn enum_variant_field_nodes(node: &Cst) -> Vec<Cst> {
    node.descendants()
        .filter(|child| child.kind() == SyntaxKind::StructField)
        .collect()
}

pub(crate) fn enum_variant_direct_type_exprs(node: &Cst) -> Vec<Cst> {
    node.children()
        .filter(|child| child.kind() == SyntaxKind::TypeExpr)
        .collect()
}

fn collect_pre_with_descendants(node: &Cst, kind: SyntaxKind, out: &mut Vec<Cst>) {
    for item in node.children_with_tokens() {
        match item {
            NodeOrToken::Token(token) if token.kind() == SyntaxKind::With => break,
            NodeOrToken::Node(child) if child.kind() == kind => out.push(child),
            NodeOrToken::Node(child) => collect_pre_with_descendants(&child, kind, out),
            NodeOrToken::Token(_) => {}
        }
    }
}

fn role_input_names(node: &Cst) -> Vec<String> {
    let Some(type_expr) = child_node(node, SyntaxKind::TypeExpr) else {
        return Vec::new();
    };
    let mut out = Vec::new();
    for token in type_expr
        .descendants_with_tokens()
        .filter_map(|item| item.into_token())
    {
        if token.kind() != SyntaxKind::SigilIdent {
            continue;
        }
        let name = token.text().trim_start_matches('\'').to_string();
        if !out.contains(&name) {
            out.push(name);
        }
    }
    out
}

fn role_associated_names(node: &Cst) -> Vec<String> {
    role_decl_body(node)
        .into_iter()
        .flat_map(|body| body.children())
        .filter(|child| child.kind() == SyntaxKind::TypeDecl)
        .filter_map(|child| type_decl_name(&child))
        .map(|name| name.0)
        .collect()
}

pub(crate) fn type_with_body(node: &Cst) -> Option<Cst> {
    let mut seen_with = false;
    for item in node.children_with_tokens() {
        match item {
            NodeOrToken::Token(token) if token.kind() == SyntaxKind::With => {
                seen_with = true;
            }
            NodeOrToken::Node(child)
                if seen_with
                    && matches!(
                        child.kind(),
                        SyntaxKind::BraceGroup | SyntaxKind::IndentBlock
                    ) =>
            {
                return Some(child);
            }
            _ => {}
        }
    }
    None
}

pub(crate) fn type_self_struct_node(node: &Cst) -> Option<Cst> {
    type_with_body(node)?.children().find(|child| {
        child.kind() == SyntaxKind::StructDecl
            && type_decl_name(child).is_some_and(|name| name.0 == "self")
    })
}

pub(crate) fn role_decl_body(node: &Cst) -> Option<Cst> {
    for item in node.children_with_tokens() {
        match item {
            NodeOrToken::Node(child)
                if matches!(
                    child.kind(),
                    SyntaxKind::BraceGroup | SyntaxKind::IndentBlock
                ) =>
            {
                return Some(child);
            }
            _ => {}
        }
    }
    None
}

pub(crate) fn role_impl_body(node: &Cst) -> Option<Cst> {
    for item in node.children_with_tokens() {
        match item {
            NodeOrToken::Node(child)
                if matches!(
                    child.kind(),
                    SyntaxKind::BraceGroup | SyntaxKind::IndentBlock
                ) =>
            {
                return Some(child);
            }
            _ => {}
        }
    }
    None
}

pub(crate) fn act_decl_body(node: &Cst) -> Option<Cst> {
    for item in node.children_with_tokens() {
        match item {
            NodeOrToken::Node(child)
                if matches!(
                    child.kind(),
                    SyntaxKind::BraceGroup | SyntaxKind::IndentBlock
                ) =>
            {
                return Some(child);
            }
            _ => {}
        }
    }
    None
}

pub(crate) fn act_operation_binding(node: &Cst) -> bool {
    if type_method_binding(node).is_some() || child_node(node, SyntaxKind::BindingBody).is_some() {
        return false;
    }
    child_node(node, SyntaxKind::BindingHeader)
        .is_some_and(|header| contains_node_kind(&header, SyntaxKind::TypeAnn))
}

fn act_operation_names(node: &Cst) -> Vec<Name> {
    act_decl_body(node)
        .into_iter()
        .flat_map(|body| body.children())
        .filter(|child| child.kind() == SyntaxKind::Binding && act_operation_binding(child))
        .filter_map(|binding| binding_name(&binding))
        .collect()
}

fn module_type_kind(kind: SyntaxKind) -> Option<ModuleTypeKind> {
    match kind {
        SyntaxKind::TypeDecl => Some(ModuleTypeKind::TypeAlias),
        SyntaxKind::StructDecl => Some(ModuleTypeKind::Struct),
        SyntaxKind::EnumDecl => Some(ModuleTypeKind::Enum),
        SyntaxKind::ErrorDecl => Some(ModuleTypeKind::Error),
        SyntaxKind::RoleDecl => Some(ModuleTypeKind::Role),
        SyntaxKind::ActDecl => Some(ModuleTypeKind::Act),
        _ => None,
    }
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
    fn registers_struct_and_enum_constructors_as_values() {
        let cst = parse("struct Box 'a { value: 'a }\nenum opt 'a = none | some 'a\n");
        let lower = lower_module_map(&cst);
        let root = lower.modules.root_id();

        assert_eq!(
            lower.modules.value_decls(root, &Name("Box".into())).len(),
            1
        );
        assert_eq!(
            lower.modules.value_decls(root, &Name("none".into())).len(),
            1
        );
        assert_eq!(
            lower.modules.value_decls(root, &Name("some".into())).len(),
            1
        );
    }

    #[test]
    fn role_impl_body_gets_poly_module_identity() {
        let cst = parse("role Eq 'a;\nimpl int: Eq {\n  our x.eq = x\n  my helper = x\n}\n");
        let lower = lower_module_map(&cst);
        let root = lower.modules.root_id();
        let [impl_decl] = lower.modules.role_impls(root) else {
            panic!("impl should be registered once");
        };
        let Some(Def::Mod { children, .. }) = lower.arena.defs.get(impl_decl.def) else {
            panic!("impl should have a poly module def");
        };

        assert!(lower.arena.roots.contains(&impl_decl.def));
        assert_eq!(children.len(), 2);
        assert_eq!(children[0], impl_decl.methods[0].def);
        assert_eq!(
            lower
                .modules
                .value_decls(impl_decl.body_module, &Name("helper".into()))
                .len(),
            1
        );
    }

    #[test]
    fn collects_use_aliases() {
        let cst = parse("use a::b as c\nuse x::y::*\nmy f = 1\n");
        let lower = lower_module_map(&cst);
        let root = lower.modules.root_id();
        // alias c と glob x::y の 2 本が溜まり、pass1 完了後に import view へ展開される。
        assert_eq!(lower.modules.aliases(root).len(), 2);
        assert_eq!(lower.modules.value_decls(root, &Name("f".into())).len(), 1);
    }

    #[test]
    fn import_view_resolves_aliases_across_namespaces() {
        let cst = parse(
            "mod m:\n  type T\n  my value = 1\n  mod n:\n    type U\nuse m::T as AliasT\nuse m::value as imported_value\nuse m::n as imported_n\nmy site = imported_value\n",
        );
        let lower = lower_module_map(&cst);
        let root = lower.modules.root_id();
        let m = lower.modules.module_decls(root, &Name("m".into()))[0].module;
        let n = lower.modules.module_decls(m, &Name("n".into()))[0].module;
        let value = lower.modules.value_decls(m, &Name("value".into()))[0].def;
        let site_order = lower.modules.value_decls(root, &Name("site".into()))[0].order;
        let alias_t = lower
            .modules
            .lexical_type_at(root, &Name("AliasT".into()), site_order)
            .expect("type alias import should resolve");

        assert_eq!(
            lower.modules.type_decl_path(&alias_t).segments,
            vec![Name("m".into()), Name("T".into())]
        );
        assert_eq!(
            lower
                .modules
                .lexical_value_at(root, &Name("imported_value".into()), site_order),
            Some(value)
        );
        assert_eq!(
            lower
                .modules
                .lexical_module_at(root, &Name("imported_n".into()), site_order),
            Some(n)
        );
    }

    #[test]
    fn import_view_resolves_globs_across_namespaces() {
        let cst = parse(
            "mod m:\n  type T\n  my value = 1\n  mod n:\n    type U\nuse m::*\nmy site = value\n",
        );
        let lower = lower_module_map(&cst);
        let root = lower.modules.root_id();
        let m = lower.modules.module_decls(root, &Name("m".into()))[0].module;
        let n = lower.modules.module_decls(m, &Name("n".into()))[0].module;
        let value = lower.modules.value_decls(m, &Name("value".into()))[0].def;
        let site_order = lower.modules.value_decls(root, &Name("site".into()))[0].order;
        let imported_t = lower
            .modules
            .lexical_type_at(root, &Name("T".into()), site_order)
            .expect("glob type import should resolve");

        assert_eq!(
            lower.modules.type_decl_path(&imported_t).segments,
            vec![Name("m".into()), Name("T".into())]
        );
        assert_eq!(
            lower
                .modules
                .lexical_value_at(root, &Name("value".into()), site_order),
            Some(value)
        );
        assert_eq!(
            lower
                .modules
                .lexical_module_at(root, &Name("n".into()), site_order),
            Some(n)
        );
    }

    #[test]
    fn direct_type_decl_shadows_glob_import() {
        let cst = parse("mod m:\n  type T\nuse m::*\ntype T\nmy site = 1\n");
        let lower = lower_module_map(&cst);
        let root = lower.modules.root_id();
        let site_order = lower.modules.value_decls(root, &Name("site".into()))[0].order;
        let found = lower
            .modules
            .lexical_type_at(root, &Name("T".into()), site_order)
            .expect("local type should resolve");

        assert_eq!(
            lower.modules.type_decl_path(&found).segments,
            vec![Name("T".into())]
        );
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
    fn registers_type_namespace_decls_and_constructor_roots() {
        let cst = parse(
            "type Alias\nstruct Record { x: int }\nenum Choice { A }\nerror Failure:\n  bad str\nrole Eq;\nact Console;\nmy value = 1\n",
        );
        let lower = lower_module_map(&cst);
        let root = lower.modules.root_id();

        assert_eq!(lower.arena.roots.len(), 4);
        assert_eq!(
            lower
                .modules
                .value_decls(root, &Name("Record".into()))
                .len(),
            1
        );
        assert_eq!(lower.modules.value_decls(root, &Name("A".into())).len(), 1);
        assert_eq!(
            lower.modules.value_decls(root, &Name("bad".into())).len(),
            1
        );
        assert_eq!(
            lower.modules.type_decls(root, &Name("Alias".into()))[0].kind,
            ModuleTypeKind::TypeAlias
        );
        assert_eq!(
            lower.modules.type_decls(root, &Name("Record".into()))[0].kind,
            ModuleTypeKind::Struct
        );
        assert_eq!(
            lower.modules.type_decls(root, &Name("Choice".into()))[0].kind,
            ModuleTypeKind::Enum
        );
        assert_eq!(
            lower.modules.type_decls(root, &Name("Failure".into()))[0].kind,
            ModuleTypeKind::Error
        );
        assert_eq!(
            lower.modules.type_decls(root, &Name("Eq".into()))[0].kind,
            ModuleTypeKind::Role
        );
        assert_eq!(
            lower.modules.type_decls(root, &Name("Console".into()))[0].kind,
            ModuleTypeKind::Act
        );
    }

    #[test]
    fn registers_type_with_body_as_companion_module_methods() {
        let cst =
            parse("type box 'a with:\n  our x.value = x\n  our &x.update = &x\nmy site = 1\n");
        let lower = lower_module_map(&cst);
        let root = lower.modules.root_id();
        let box_type = lower.modules.type_decls(root, &Name("box".into()))[0].clone();
        let companion = lower
            .modules
            .type_companion(box_type.id)
            .expect("type with should create a companion module");
        let methods = lower.modules.type_methods(box_type.id);

        assert_eq!(
            lower.modules.module_decls(root, &Name("box".into()))[0].module,
            companion
        );
        assert_eq!(
            lower
                .modules
                .value_decls(companion, &Name("value".into()))
                .len(),
            1
        );
        assert_eq!(
            lower
                .modules
                .value_decls(companion, &Name("update!".into()))
                .len(),
            1
        );
        assert_eq!(methods.len(), 2);
        assert_eq!(methods[0].name, Name("value".into()));
        assert_eq!(methods[0].receiver, Name("x".into()));
        assert_eq!(methods[0].receiver_kind, TypeMethodReceiver::Value);
        assert_eq!(methods[1].name, Name("update".into()));
        assert_eq!(methods[1].receiver, Name("&x".into()));
        assert_eq!(methods[1].receiver_kind, TypeMethodReceiver::Ref);
    }

    #[test]
    fn registers_type_with_self_struct_as_outer_constructor() {
        let cst = parse("type t 'a with:\n  struct self:\n    field: 'a\n");
        let lower = lower_module_map(&cst);
        let root = lower.modules.root_id();
        let t_type = lower.modules.type_decls(root, &Name("t".into()))[0].clone();
        let companion = lower
            .modules
            .type_companion(t_type.id)
            .expect("type with should create companion module");

        assert_eq!(lower.modules.value_decls(root, &Name("t".into())).len(), 1);
        assert!(
            lower
                .modules
                .type_decls(companion, &Name("self".into()))
                .is_empty()
        );
    }

    #[test]
    fn registers_act_operation_names_for_coverage() {
        let cst = parse(
            "act out:\n  our say: int -> unit\n  our write: int -> unit\n  our x.clear = x\nmy site = 1\n",
        );
        let lower = lower_module_map(&cst);
        let root = lower.modules.root_id();
        let site = lower.modules.value_decls(root, &Name("site".into()))[0].order;
        let ops = lower
            .modules
            .act_operation_decls_at(root, &[Name("out".into())], site)
            .into_iter()
            .map(|op| op.name)
            .collect::<Vec<_>>();

        assert_eq!(ops, vec![Name("say".into()), Name("write".into())]);
    }

    #[test]
    fn registers_act_body_as_companion_module_effect_methods() {
        let cst = parse("act out:\n  our say: int -> unit\n  our x.clear = x\nmy site = 1\n");
        let lower = lower_module_map(&cst);
        let root = lower.modules.root_id();
        let out = lower.modules.type_decls(root, &Name("out".into()))[0].clone();
        let companion = lower
            .modules
            .type_companion(out.id)
            .expect("act body should create a companion module");
        let methods = lower.modules.act_methods(out.id);

        assert_eq!(
            lower.modules.module_decls(root, &Name("out".into()))[0].module,
            companion
        );
        assert_eq!(methods.len(), 1);
        assert_eq!(methods[0].name, Name("clear".into()));
        assert_eq!(methods[0].receiver, Name("x".into()));
        assert!(
            lower
                .modules
                .value_decls(companion, &Name("say".into()))
                .is_empty()
        );
    }

    #[test]
    fn registers_role_body_as_companion_module_role_methods() {
        let cst = parse("role Display 'a:\n  type out\n  our x.display: out\nmy site = 1\n");
        let lower = lower_module_map(&cst);
        let root = lower.modules.root_id();
        let display = lower.modules.type_decls(root, &Name("Display".into()))[0].clone();
        let companion = lower
            .modules
            .type_companion(display.id)
            .expect("role body should create a companion module");
        let methods = lower.modules.role_methods(display.id);

        assert_eq!(lower.modules.role_inputs(display.id), &["a".to_string()]);
        assert_eq!(
            lower.modules.role_associated(display.id),
            &["out".to_string()]
        );
        assert_eq!(
            lower.modules.module_decls(root, &Name("Display".into()))[0].module,
            companion
        );
        assert_eq!(
            lower
                .modules
                .value_decls(companion, &Name("display".into()))
                .len(),
            1
        );
        assert_eq!(methods.len(), 1);
        assert_eq!(methods[0].name, Name("display".into()));
        assert_eq!(methods[0].receiver, Some(Name("x".into())));
        assert_eq!(methods[0].vis, Vis::Our);
    }

    #[test]
    fn lexical_type_lookup_converts_child_site_to_parent_module_order() {
        let cst = parse("type User\nmod m:\n  my y = 1\n");
        let lower = lower_module_map(&cst);
        let root = lower.modules.root_id();
        let m = lower.modules.module_decls(root, &Name("m".into()))[0].module;
        let y_order = lower.modules.value_decls(m, &Name("y".into()))[0].order;

        assert_eq!(
            lower
                .modules
                .lexical_type_at(m, &Name("User".into()), y_order)
                .map(|decl| decl.kind),
            Some(ModuleTypeKind::TypeAlias)
        );
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
