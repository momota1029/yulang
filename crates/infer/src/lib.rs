//! `infer` は、`sources` の CST から `poly` IR と型情報を作るための作業 crate。
//!
//! この crate は最終 IR ではなく、推論中に増える状態を持つ。たとえば constraint machine、
//! use-site 型 table、selection watcher、open SCC graph はここに置く。`poly` 側は最終的に
//! 読まれる構造と解決結果だけを保持する。
//!
//! 現在の入口は pass1: CST を走査してモジュールマップを作る段階と、pass2 first cut:
//! binding body を `ExprLowerer` で lower して `Def::Let.body` と `DefId` 型 slot を埋める段階。
//! 型定義系の本体 lowering はまだこの足場へ接続していない。

mod act_resolve;
pub mod analysis;
pub mod annotation;
pub mod arena;
mod builtin_ops;
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
mod std_paths;
pub mod typing;
pub mod uses;

pub use arena::Arena;

use crate::act_resolve::{ActTypeExpr, ActTypeResolver};
use poly::dump::DumpLabels;
use poly::expr::{Arena as PolyArena, Def, DefId, Vis};
use rowan::{NodeOrToken, SyntaxNode};
use rustc_hash::{FxHashMap, FxHashSet};
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
    pub def: Option<DefId>,
    pub signature: Option<SyntaxNode<YulangLanguage>>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct ActOperationSig {
    name: Name,
    signature: Option<SyntaxNode<YulangLanguage>>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct ActOperationDef {
    effect: TypeDeclId,
    name: Name,
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
pub struct TypeFieldMethodDecl {
    pub owner: TypeDeclId,
    pub name: Name,
    pub receiver_kind: TypeMethodReceiver,
    pub def: DefId,
    pub vis: Vis,
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
    act_templates: FxHashMap<TypeDeclId, Cst>,
    act_copies: FxHashMap<TypeDeclId, ActCopyDecl>,
    resolved_act_copies: FxHashMap<TypeDeclId, ResolvedActCopyDecl>,
    synthetic_var_act_copies: FxHashSet<TypeDeclId>,
    synthetic_var_act_uses: FxHashMap<DefId, Vec<SyntheticVarActUse>>,
    act_ops: FxHashMap<TypeDeclId, Vec<ActOperationSig>>,
    act_op_defs: FxHashMap<DefId, ActOperationDef>,
    lazy_ops: FxHashSet<DefId>,
    act_methods: FxHashMap<TypeDeclId, Vec<ActMethodDecl>>,
    role_inputs: FxHashMap<TypeDeclId, Vec<String>>,
    role_associated: FxHashMap<TypeDeclId, Vec<String>>,
    role_impls: FxHashMap<ModuleId, Vec<RoleImplDecl>>,
    role_methods: FxHashMap<TypeDeclId, Vec<RoleMethodDecl>>,
    type_companions: FxHashMap<TypeDeclId, ModuleId>,
    type_methods: FxHashMap<TypeDeclId, Vec<TypeMethodDecl>>,
    type_field_methods: FxHashMap<TypeDeclId, Vec<TypeFieldMethodDecl>>,
    next_type_id: u32,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct ActCopyDecl {
    pub source: Cst,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct ResolvedActCopyDecl {
    pub source: TypeDeclId,
    pub type_var_aliases: Vec<(String, String)>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct SyntheticVarActUse {
    pub source: Name,
    pub act: TypeDeclId,
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
            act_templates: FxHashMap::default(),
            act_copies: FxHashMap::default(),
            resolved_act_copies: FxHashMap::default(),
            synthetic_var_act_copies: FxHashSet::default(),
            synthetic_var_act_uses: FxHashMap::default(),
            act_ops: FxHashMap::default(),
            act_op_defs: FxHashMap::default(),
            lazy_ops: FxHashSet::default(),
            act_methods: FxHashMap::default(),
            role_inputs: FxHashMap::default(),
            role_associated: FxHashMap::default(),
            role_impls: FxHashMap::default(),
            role_methods: FxHashMap::default(),
            type_companions: FxHashMap::default(),
            type_methods: FxHashMap::default(),
            type_field_methods: FxHashMap::default(),
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
    fn set_act_ops(&mut self, id: TypeDeclId, ops: Vec<ActOperationSig>) {
        self.act_ops.insert(id, ops);
    }
    fn insert_act_operation_def(&mut self, owner: TypeDeclId, name: Name, def: DefId) {
        self.act_op_defs.insert(
            def,
            ActOperationDef {
                effect: owner,
                name,
            },
        );
    }
    pub(crate) fn is_act_operation_def(&self, def: DefId) -> bool {
        self.act_op_defs.contains_key(&def)
    }
    fn mark_lazy_op(&mut self, def: DefId) {
        self.lazy_ops.insert(def);
    }
    pub(crate) fn is_lazy_op(&self, def: DefId) -> bool {
        self.lazy_ops.contains(&def)
    }
    fn set_act_template(&mut self, id: TypeDeclId, node: Cst) {
        self.act_templates.insert(id, node);
    }
    pub(crate) fn act_template(&self, id: TypeDeclId) -> Option<&Cst> {
        self.act_templates.get(&id)
    }
    fn set_act_copy(&mut self, id: TypeDeclId, copy: ActCopyDecl) {
        self.act_copies.insert(id, copy);
    }
    pub(crate) fn act_copy(&self, id: TypeDeclId) -> Option<&ActCopyDecl> {
        self.act_copies.get(&id)
    }
    fn set_resolved_act_copy(&mut self, id: TypeDeclId, copy: ResolvedActCopyDecl) {
        self.resolved_act_copies.insert(id, copy);
    }
    pub(crate) fn resolved_act_copy(&self, id: TypeDeclId) -> Option<&ResolvedActCopyDecl> {
        self.resolved_act_copies.get(&id)
    }
    fn set_synthetic_var_act_copy(&mut self, id: TypeDeclId) {
        self.synthetic_var_act_copies.insert(id);
    }
    pub(crate) fn synthetic_var_act_copy_ids(&self) -> Vec<TypeDeclId> {
        self.synthetic_var_act_copies.iter().copied().collect()
    }
    fn push_synthetic_var_act_use(&mut self, owner: DefId, usage: SyntheticVarActUse) {
        self.synthetic_var_act_uses
            .entry(owner)
            .or_default()
            .push(usage);
    }
    pub(crate) fn synthetic_var_act_uses(&self, owner: DefId) -> &[SyntheticVarActUse] {
        self.synthetic_var_act_uses
            .get(&owner)
            .map(Vec::as_slice)
            .unwrap_or(&[])
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
    fn insert_type_field_method(&mut self, method: TypeFieldMethodDecl) {
        self.type_field_methods
            .entry(method.owner)
            .or_default()
            .push(method);
    }
    pub fn type_field_methods(&self, id: TypeDeclId) -> &[TypeFieldMethodDecl] {
        self.type_field_methods
            .get(&id)
            .map(Vec::as_slice)
            .unwrap_or(&[])
    }
    pub fn all_type_field_methods(&self) -> impl Iterator<Item = &TypeFieldMethodDecl> {
        self.type_field_methods
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
            .map(|op| ActOperationDecl {
                def: self
                    .type_companion(effect.id)
                    .and_then(|companion| self.value_at(companion, &op.name, module_path_site()))
                    .filter(|def| {
                        self.act_op_defs
                            .get(def)
                            .is_some_and(|found| found.effect == effect.id && found.name == op.name)
                    }),
                effect: effect.clone(),
                name: op.name,
                signature: op.signature,
            })
            .collect()
    }
    pub fn act_operation_decl_by_def(&self, def: DefId) -> Option<ActOperationDecl> {
        let op = self.act_op_defs.get(&def)?;
        let effect = self.type_decl_by_id(op.effect)?;
        let signature = self
            .act_ops
            .get(&op.effect)
            .and_then(|ops| ops.iter().find(|sig| sig.name == op.name))
            .and_then(|sig| sig.signature.clone());
        Some(ActOperationDecl {
            effect,
            name: op.name.clone(),
            def: Some(def),
            signature,
        })
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
    fn module_def(&self, module: ModuleId) -> Option<DefId> {
        let parent = self.nodes[module.0].parent?;
        let parent_node = &self.nodes[parent.module.0];
        parent_node.decls.iter().find_map(|decl| {
            (decl.order == parent.order)
                .then_some(decl)
                .and_then(|decl| match decl.kind {
                    ModuleDeclKind::Module { module: child, def } if child == module => Some(def),
                    ModuleDeclKind::Value { .. }
                    | ModuleDeclKind::Type { .. }
                    | ModuleDeclKind::Module { .. } => None,
                })
        })
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
                self.import_op_aliases(module, name, path, alias.order);
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
    /// 名前指定 import の op symbol 展開。`use foo::(+)` は plain name `+` として届くので、
    /// 各 fixity の mangled 名（`#op:infix:+` 等）でも値を引き、見つかったものを全部運ぶ。
    fn import_op_aliases(
        &mut self,
        module: ModuleId,
        name: &Name,
        path: &ModulePath,
        order: ModuleOrder,
    ) {
        let Some(last) = path.segments.last().cloned() else {
            return;
        };
        for fixity in OP_FIXITY_TAGS {
            let mut op_path = path.clone();
            *op_path
                .segments
                .last_mut()
                .expect("op import path should be non-empty") = op_value_name(fixity, &last.0);
            let Some(target) = self.import_path_target(module, &op_path, order) else {
                continue;
            };
            let Some(def) = target.value else {
                continue;
            };
            self.nodes[module.0]
                .import_values
                .entry(op_value_name(fixity, &name.0))
                .or_default()
                .push(ImportedValueDecl { order, def });
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
                    self.register_binding_values(&child, module, &mut children);
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
                SyntaxKind::OpDef => {
                    if let Some(info) = op_def_info(&child) {
                        let def = self.arena.defs.fresh();
                        self.arena.defs.set(
                            def,
                            Def::Let {
                                vis: info.vis,
                                scheme: None,
                                body: None,
                                children: Vec::new(),
                            },
                        );
                        self.modules.insert_value(module, info.name, def, info.vis);
                        if info.lazy {
                            self.modules.mark_lazy_op(def);
                        }
                        children.push(def);
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
                // 型定義系の本体、Cast は後で。
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

    fn register_binding_values(
        &mut self,
        binding: &Cst,
        module: ModuleId,
        children: &mut Vec<DefId>,
    ) {
        let vis = binding_vis(binding);
        for name in binding_value_names(binding) {
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
            self.register_local_var_act_copies_in_binding(binding, module, def);
        }
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
                        self.register_local_var_act_copies_in_binding(&child, module, def);
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
                        self.register_local_var_act_copies_in_binding(&child, module, def);
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
            self.modules.set_act_template(id, node.clone());
            let copy = act_copy_decl(node);
            if let Some(copy) = copy {
                self.modules.set_act_copy(id, copy);
                self.modules.set_act_ops(id, act_operation_signatures(node));
            } else {
                self.modules.set_act_ops(id, act_operation_signatures(node));
                self.register_act_companion(node, module, name.clone(), id, vis, children);
            }
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
            self.register_type_constructors(node, module, kind, id, name.clone(), vis, children);
            self.register_type_companion(node, module, name, id, vis, children);
        }
    }

    fn register_local_var_act_copies_in_binding(
        &mut self,
        binding: &Cst,
        module: ModuleId,
        owner: DefId,
    ) {
        let Some(body) = binding_body_expr(binding) else {
            return;
        };
        for (index, local) in body
            .descendants()
            .filter(|node| node.kind() == SyntaxKind::Binding)
            .enumerate()
        {
            let Some(name) = local_var_act_name(&local) else {
                continue;
            };
            self.register_synthetic_var_act_copy(module, owner, name, index);
        }
    }

    fn register_synthetic_var_act_copy(
        &mut self,
        module: ModuleId,
        owner: DefId,
        source: Name,
        index: usize,
    ) {
        let internal_name = synthetic_var_act_internal_name(&source, owner, index);
        let id = self
            .modules
            .insert_type(module, internal_name, ModuleTypeKind::Act, Vis::My);
        self.modules.set_synthetic_var_act_copy(id);
        self.modules
            .push_synthetic_var_act_use(owner, SyntheticVarActUse { source, act: id });
    }

    fn register_type_constructors(
        &mut self,
        node: &Cst,
        module: ModuleId,
        kind: ModuleTypeKind,
        owner: TypeDeclId,
        name: Name,
        vis: Vis,
        children: &mut Vec<DefId>,
    ) {
        match kind {
            ModuleTypeKind::TypeAlias if type_self_struct_node(node).is_some() => {
                let def = self.register_synthetic_value(module, name, vis);
                children.push(def);
                if let Some(self_struct) = type_self_struct_node(node) {
                    self.register_struct_field_methods(&self_struct, owner, vis);
                }
            }
            ModuleTypeKind::Struct => {
                let def = self.register_synthetic_value(module, name, vis);
                children.push(def);
                self.register_struct_field_methods(node, owner, vis);
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

    fn register_struct_field_methods(&mut self, node: &Cst, owner: TypeDeclId, vis: Vis) {
        for field in struct_field_nodes(node) {
            let Some(name) = struct_field_name(&field) else {
                continue;
            };
            for receiver_kind in [TypeMethodReceiver::Value, TypeMethodReceiver::Ref] {
                let def = self.register_synthetic_let(vis);
                self.modules.insert_type_field_method(TypeFieldMethodDecl {
                    owner,
                    name: name.clone(),
                    receiver_kind,
                    def,
                    vis,
                });
            }
        }
    }

    fn register_synthetic_value(&mut self, module: ModuleId, name: Name, vis: Vis) -> DefId {
        let def = self.register_synthetic_let(vis);
        self.modules.insert_value(module, name, def, vis);
        def
    }

    fn register_synthetic_let(&mut self, vis: Vis) -> DefId {
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
                        self.register_local_var_act_copies_in_binding(&child, module, def);
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
                        self.register_local_var_act_copies_in_binding(&child, module, def);
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
                SyntaxKind::Binding if act_operation_binding(&child) => {
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
                    self.modules.insert_value(module, name.clone(), def, vis);
                    self.modules.insert_act_operation_def(owner, name, def);
                }
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
                    self.register_local_var_act_copies_in_binding(&child, module, def);
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
                    self.register_local_var_act_copies_in_binding(&child, module, def);
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
                        self.register_local_var_act_copies_in_binding(&child, module, def);
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
                        self.register_local_var_act_copies_in_binding(&child, module, def);
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

    fn append_created_module_to_parent(&mut self, module: ModuleId, def: DefId) {
        if module == self.modules.root_id() {
            self.arena.roots.push(def);
            return;
        }
        let Some(parent_def) = self.modules.module_def(module) else {
            return;
        };
        self.append_module_children(parent_def, vec![def]);
    }

    fn finalize_act_copies(&mut self) {
        let ids = self.modules.act_copies.keys().copied().collect::<Vec<_>>();
        for id in ids {
            self.finalize_act_copy(id);
        }
        let synthetic_ids = self.modules.synthetic_var_act_copy_ids();
        for id in synthetic_ids {
            self.finalize_synthetic_var_act_copy(id);
        }
    }

    fn finalize_act_copy(&mut self, id: TypeDeclId) {
        let Some(dest) = self.modules.type_decl_by_id(id) else {
            return;
        };
        let Some(resolved) = self.resolve_act_copy(&dest) else {
            return;
        };
        let own_body = self.modules.act_template(id).and_then(act_decl_body);
        self.materialize_act_copy(id, &dest, resolved, own_body, true);
    }

    fn finalize_synthetic_var_act_copy(&mut self, id: TypeDeclId) {
        let Some(dest) = self.modules.type_decl_by_id(id) else {
            return;
        };
        let Some(source) = self.std_var_act_decl() else {
            return;
        };
        let source_type_vars = self
            .modules
            .act_template(source.id)
            .map(act_type_var_names)
            .unwrap_or_default();
        let type_var_aliases = source_type_vars
            .into_iter()
            .map(|name| (name.clone(), name))
            .collect();
        self.materialize_act_copy(
            id,
            &dest,
            ResolvedActCopyDecl {
                source: source.id,
                type_var_aliases,
            },
            None,
            false,
        );
    }

    fn materialize_act_copy(
        &mut self,
        id: TypeDeclId,
        dest: &ModuleTypeDecl,
        resolved: ResolvedActCopyDecl,
        own_body: Option<Cst>,
        attach_to_parent: bool,
    ) {
        let Some(source_body) = self
            .modules
            .act_template(resolved.source)
            .and_then(act_decl_body)
        else {
            return;
        };
        self.modules.set_resolved_act_copy(id, resolved);

        let mut ops = act_operation_signatures_from_body(&source_body);
        push_unique_act_ops(
            &mut ops,
            self.modules.act_ops.get(&id).cloned().unwrap_or_default(),
        );
        self.modules.set_act_ops(id, ops);

        let (def, companion, created) =
            self.ensure_child_module(dest.module, dest.name.clone(), dest.vis);
        self.modules.set_type_companion(id, companion);
        let mut companion_children = self.register_act_companion_block(&source_body, companion, id);
        if let Some(own_body) = own_body {
            companion_children.extend(self.register_act_companion_block(&own_body, companion, id));
        }
        self.append_module_children(def, companion_children);
        if created && attach_to_parent {
            self.append_created_module_to_parent(dest.module, def);
        }
    }

    fn std_var_act_decl(&self) -> Option<ModuleTypeDecl> {
        let path = crate::std_paths::control_var_var_act()
            .into_iter()
            .map(Name)
            .collect::<Vec<_>>();
        self.modules
            .type_path_at(self.modules.root_id(), &path, module_path_site())
            .filter(|decl| decl.kind == ModuleTypeKind::Act)
    }

    fn resolve_act_copy(&self, dest: &ModuleTypeDecl) -> Option<ResolvedActCopyDecl> {
        let copy = self.modules.act_copy(dest.id)?;
        let resolver = ActTypeResolver::new(&self.modules, dest.module, dest.order);
        let source_use = resolver.resolve_act_use(&copy.source).ok()?;
        let source_decl = source_use.decl;
        let source_type_vars = self
            .modules
            .act_template(source_decl.id)
            .map(act_type_var_names)
            .unwrap_or_default();
        let type_var_aliases = source_type_vars
            .into_iter()
            .zip(source_use.args.iter())
            .filter_map(|(source, arg)| act_type_var_arg_name(arg).map(|target| (source, target)))
            .collect();
        Some(ResolvedActCopyDecl {
            source: source_decl.id,
            type_var_aliases,
        })
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
    lower.finalize_act_copies();
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
    lower.finalize_act_copies();
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

/// `Binding → BindingHeader → Pattern` から module value として登録する名前を読む。
fn binding_name(node: &Cst) -> Option<Name> {
    binding_value_names(node).into_iter().next()
}

fn binding_value_names(node: &Cst) -> Vec<Name> {
    let Some(header) = child_node(node, SyntaxKind::BindingHeader) else {
        return Vec::new();
    };
    let Some(pattern) = child_node(&header, SyntaxKind::Pattern) else {
        return Vec::new();
    };
    if contains_node_kind(&pattern, SyntaxKind::ApplyML)
        || contains_node_kind(&pattern, SyntaxKind::ApplyC)
        || contains_node_kind(&pattern, SyntaxKind::TypeAnn)
        || pattern_field_name(&pattern).is_some()
    {
        return pattern_head_binding_name(&pattern).into_iter().collect();
    }
    let mut out = Vec::new();
    collect_pattern_binding_names(&pattern, &mut out);
    out
}

fn binding_pattern(node: &Cst) -> Option<Cst> {
    let header = child_node(node, SyntaxKind::BindingHeader)?;
    child_node(&header, SyntaxKind::Pattern)
}

fn binding_has_single_head_pattern(node: &Cst) -> bool {
    let Some(pattern) = binding_pattern(node) else {
        return false;
    };
    pattern_head_binding_name(&pattern).is_some()
}

fn pattern_head_binding_name(pattern: &Cst) -> Option<Name> {
    match first_pattern_token_or_group(pattern)? {
        NodeOrToken::Token(token)
            if matches!(token.kind(), SyntaxKind::Ident | SyntaxKind::SigilIdent) =>
        {
            let name = Name(token.text().to_string());
            (name.0 != "_").then_some(name)
        }
        NodeOrToken::Node(group) if group.kind() == SyntaxKind::PatParenGroup => {
            pattern_head_binding_name(&single_pattern_child(&group)?)
        }
        _ => None,
    }
}

fn collect_pattern_binding_names(pattern: &Cst, out: &mut Vec<Name>) {
    if pattern.kind() == SyntaxKind::PatParenGroup {
        for child in pattern
            .children()
            .filter(|child| child.kind() == SyntaxKind::Pattern)
        {
            collect_pattern_binding_names(&child, out);
        }
        return;
    }

    let Some(item) = single_pattern_token_or_group(pattern) else {
        return;
    };
    match item {
        NodeOrToken::Token(token)
            if matches!(token.kind(), SyntaxKind::Ident | SyntaxKind::SigilIdent) =>
        {
            let name = Name(token.text().to_string());
            if name.0 != "_" {
                out.push(name);
            }
        }
        NodeOrToken::Node(group) if group.kind() == SyntaxKind::PatParenGroup => {
            collect_pattern_binding_names(&group, out);
        }
        _ => {}
    }
}

fn single_pattern_token_or_group(
    pattern: &Cst,
) -> Option<NodeOrToken<Cst, rowan::SyntaxToken<YulangLanguage>>> {
    let mut items = pattern
        .children_with_tokens()
        .filter(|item| !item_is_trivia(item));
    let first = items.next()?;
    items.next().is_none().then_some(first)
}

fn first_pattern_token_or_group(
    pattern: &Cst,
) -> Option<NodeOrToken<Cst, rowan::SyntaxToken<YulangLanguage>>> {
    pattern
        .children_with_tokens()
        .find(|item| !item_is_trivia(item))
}

fn single_pattern_child(group: &Cst) -> Option<Cst> {
    let mut patterns = group
        .children()
        .filter(|child| child.kind() == SyntaxKind::Pattern);
    let first = patterns.next()?;
    patterns.next().is_none().then_some(first)
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

fn binding_body_expr(binding: &Cst) -> Option<Cst> {
    let body = child_node(binding, SyntaxKind::BindingBody)?;
    body.children().find(|child| {
        matches!(
            child.kind(),
            SyntaxKind::Expr | SyntaxKind::IndentBlock | SyntaxKind::BraceGroup
        )
    })
}

fn local_var_act_name(binding: &Cst) -> Option<Name> {
    let source = binding_name(binding)?;
    let base = source.0.strip_prefix('$')?;
    (!base.is_empty()).then(|| Name(format!("&{base}")))
}

fn synthetic_var_act_internal_name(source: &Name, owner: DefId, index: usize) -> Name {
    Name(format!("{}#{}:{index}", source.0, owner.0))
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

pub(crate) fn act_type_var_names(node: &Cst) -> Vec<String> {
    let mut out = Vec::new();
    let mut seen_act_name = false;
    for item in node.children_with_tokens() {
        match item {
            NodeOrToken::Token(token) if token.kind() == SyntaxKind::Ident && !seen_act_name => {
                seen_act_name = true;
            }
            NodeOrToken::Token(token)
                if matches!(
                    token.kind(),
                    SyntaxKind::Equal
                        | SyntaxKind::With
                        | SyntaxKind::Colon
                        | SyntaxKind::BraceL
                        | SyntaxKind::Semicolon
                ) =>
            {
                break;
            }
            NodeOrToken::Node(child)
                if matches!(
                    child.kind(),
                    SyntaxKind::IndentBlock | SyntaxKind::BraceGroup
                ) =>
            {
                break;
            }
            NodeOrToken::Node(child) if seen_act_name && child.kind() == SyntaxKind::TypeExpr => {
                if let Some(name) = bare_type_var_expr(&child)
                    && !out.contains(&name)
                {
                    out.push(name);
                }
            }
            _ => {}
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

fn act_operation_signatures(node: &Cst) -> Vec<ActOperationSig> {
    act_decl_body(node)
        .into_iter()
        .flat_map(|body| act_operation_signatures_from_body(&body))
        .collect()
}

fn act_operation_signatures_from_body(body: &Cst) -> Vec<ActOperationSig> {
    body.children()
        .filter(|child| child.kind() == SyntaxKind::Binding && act_operation_binding(child))
        .filter_map(|binding| {
            Some(ActOperationSig {
                name: binding_name(&binding)?,
                signature: binding_type_expr(&binding),
            })
        })
        .collect()
}

fn act_copy_decl(node: &Cst) -> Option<ActCopyDecl> {
    let source = act_copy_source_type_expr(node)?;
    Some(ActCopyDecl { source })
}

fn act_copy_source_type_expr(node: &Cst) -> Option<Cst> {
    let mut after_equal = false;
    for item in node.children_with_tokens() {
        match item {
            NodeOrToken::Token(token) if token.kind() == SyntaxKind::Equal => {
                after_equal = true;
            }
            NodeOrToken::Node(child) if after_equal && child.kind() == SyntaxKind::TypeExpr => {
                return Some(child);
            }
            _ => {}
        }
    }
    None
}

fn bare_type_var_expr(type_expr: &Cst) -> Option<String> {
    let items = type_expr
        .children_with_tokens()
        .filter(|item| !item_is_trivia(item))
        .collect::<Vec<_>>();
    let [NodeOrToken::Token(token)] = items.as_slice() else {
        return None;
    };
    (token.kind() == SyntaxKind::SigilIdent)
        .then(|| token.text().trim_start_matches('\'').to_string())
}

fn act_type_var_arg_name(arg: &ActTypeExpr) -> Option<String> {
    match arg {
        ActTypeExpr::Var(name) => Some(name.clone()),
        ActTypeExpr::Builtin(_)
        | ActTypeExpr::Named(_)
        | ActTypeExpr::Apply { .. }
        | ActTypeExpr::Function { .. } => None,
    }
}

fn push_unique_act_ops(out: &mut Vec<ActOperationSig>, ops: Vec<ActOperationSig>) {
    for op in ops {
        if !out.iter().any(|existing| existing.name == op.name) {
            out.push(op);
        }
    }
}

fn item_is_trivia(item: &NodeOrToken<Cst, rowan::SyntaxToken<YulangLanguage>>) -> bool {
    item.as_token()
        .is_some_and(|token| matches!(token.kind(), SyntaxKind::Space | SyntaxKind::LineComment))
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
pub(crate) const OP_FIXITY_TAGS: [&str; 4] = ["prefix", "infix", "suffix", "nullfix"];

/// op を value namespace に置くときの mangled 名。fixity 違いは別の値として共存する。
/// `#` 始まりは通常の識別子になり得ないため、ユーザ名と衝突しない。
pub(crate) fn op_value_name(fixity: &str, symbol: &str) -> Name {
    Name(format!("#op:{fixity}:{symbol}"))
}

pub(crate) struct OpDefInfo {
    pub(crate) name: Name,
    pub(crate) vis: Vis,
    pub(crate) lazy: bool,
    pub(crate) nullfix: bool,
}

/// OpDef ノードのヘッダから登録に要る情報を読む。bps は infer では使わない。
pub(crate) fn op_def_info(node: &Cst) -> Option<OpDefInfo> {
    let header = child_node(node, SyntaxKind::OpDefHeader)?;
    let symbol = header
        .children_with_tokens()
        .filter_map(|item| item.into_token())
        .find(|tok| tok.kind() == SyntaxKind::OpName)
        .map(|tok| tok.text().to_string())?;
    let fixity = header
        .children_with_tokens()
        .filter_map(|item| item.into_token())
        .find_map(|tok| match tok.kind() {
            SyntaxKind::Prefix => Some("prefix"),
            SyntaxKind::Infix => Some("infix"),
            SyntaxKind::Suffix => Some("suffix"),
            SyntaxKind::Nullfix => Some("nullfix"),
            _ => None,
        })?;
    let lazy = header
        .children_with_tokens()
        .filter_map(|item| item.into_token())
        .any(|tok| tok.kind() == SyntaxKind::Lazy);
    Some(OpDefInfo {
        name: op_value_name(fixity, &symbol),
        vis: vis_of(&header),
        lazy,
        nullfix: fixity == "nullfix",
    })
}

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
    fn registers_parenthesized_keyword_call_binding() {
        let cst = parse("pub (mod)(x: int, y: int): int\nmy site = mod\n");
        let lower = lower_module_map(&cst);
        let root = lower.modules.root_id();

        assert_eq!(
            lower.modules.value_decls(root, &Name("mod".into())).len(),
            1
        );
        assert_eq!(
            lower.modules.value_decls(root, &Name("site".into())).len(),
            1
        );
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
    fn registers_act_operation_value_defs_in_companion_scope() {
        let cst = parse("act out:\n  our say: int -> unit\nmy site = 1\n");
        let lower = lower_module_map(&cst);
        let root = lower.modules.root_id();
        let out = lower.modules.type_decls(root, &Name("out".into()))[0].clone();
        let companion = lower
            .modules
            .type_companion(out.id)
            .expect("act should create companion");
        let op_def = lower.modules.value_decls(companion, &Name("say".into()))[0].def;
        let op = lower
            .modules
            .act_operation_decl_by_def(op_def)
            .expect("operation value def should resolve to act operation");

        assert_eq!(op.effect.id, out.id);
        assert_eq!(op.name, Name("say".into()));
        assert_eq!(op.def, Some(op_def));
        assert_eq!(
            lower
                .modules
                .act_operation_decls_at(root, &[Name("out".into())], module_path_site())[0]
                .def,
            Some(op_def)
        );
    }

    #[test]
    fn registers_act_copy_body_in_destination_companion() {
        let cst = parse(
            "act loop:\n  my act last:\n    our break: () -> never\n  my act next = last\nmy site = 1\n",
        );
        let lower = lower_module_map(&cst);
        let root = lower.modules.root_id();
        let loop_act = lower.modules.type_decls(root, &Name("loop".into()))[0].clone();
        let loop_companion = lower
            .modules
            .type_companion(loop_act.id)
            .expect("outer act should create companion");
        let next = lower
            .modules
            .type_decls(loop_companion, &Name("next".into()))[0]
            .clone();
        let next_companion = lower
            .modules
            .type_companion(next.id)
            .expect("copied act should create companion");
        let ops = lower
            .modules
            .act_operation_decls_at(loop_companion, &[Name("next".into())], module_path_site())
            .into_iter()
            .map(|op| op.name)
            .collect::<Vec<_>>();

        assert_eq!(ops, vec![Name("break".into())]);
        assert!(lower.modules.module_path(next_companion).segments.len() >= 2);
    }

    #[test]
    fn registers_act_copy_from_qualified_source_path() {
        let cst = parse(
            "mod effects:\n  act base:\n    our tick: () -> never\nact local = effects::base\nmy site = 1\n",
        );
        let lower = lower_module_map(&cst);
        let root = lower.modules.root_id();
        let local = lower.modules.type_decls(root, &Name("local".into()))[0].clone();
        let site = lower.modules.value_decls(root, &Name("site".into()))[0].order;
        let ops = lower
            .modules
            .act_operation_decls_at(root, &[Name("local".into())], site)
            .into_iter()
            .map(|op| op.name)
            .collect::<Vec<_>>();

        assert_eq!(ops, vec![Name("tick".into())]);
        assert!(lower.modules.type_companion(local.id).is_some());
    }

    #[test]
    fn registers_act_copy_from_import_alias_after_import_view() {
        let cst = parse(
            "mod effects:\n  act base:\n    our tick: () -> never\nuse effects::base as copied\nact local = copied\nmy site = 1\n",
        );
        let lower = lower_module_map(&cst);
        let root = lower.modules.root_id();
        let site = lower.modules.value_decls(root, &Name("site".into()))[0].order;
        let ops = lower
            .modules
            .act_operation_decls_at(root, &[Name("local".into())], site)
            .into_iter()
            .map(|op| op.name)
            .collect::<Vec<_>>();

        assert_eq!(ops, vec![Name("tick".into())]);
    }

    #[test]
    fn resolves_act_copy_type_arg_aliases() {
        let cst = parse("act source 'a:\n  our tick: 'a -> never\nact local 't = source 't\n");
        let lower = lower_module_map(&cst);
        let root = lower.modules.root_id();
        let local = lower.modules.type_decls(root, &Name("local".into()))[0].clone();
        let resolved = lower
            .modules
            .resolved_act_copy(local.id)
            .expect("act copy type should resolve");

        assert_eq!(
            resolved.type_var_aliases,
            vec![("a".to_string(), "t".to_string())]
        );
    }

    #[test]
    fn act_resolution_accepts_strict_function_type_args_without_aliasing() {
        let cst = parse(
            "type a\ntype b\ntype c\nact source 'f:\n  our tick: unit -> never\nact local = source (a -> b -> c)\n",
        );
        let lower = lower_module_map(&cst);
        let root = lower.modules.root_id();
        let local = lower.modules.type_decls(root, &Name("local".into()))[0].clone();
        let resolved = lower
            .modules
            .resolved_act_copy(local.id)
            .expect("strict act use should resolve");

        assert!(resolved.type_var_aliases.is_empty());
    }

    #[test]
    fn act_resolution_rejects_non_act_head() {
        let cst = parse("type source\nact local = source\n");
        let lower = lower_module_map(&cst);
        let root = lower.modules.root_id();
        let local = lower.modules.type_decls(root, &Name("local".into()))[0].clone();

        assert!(lower.modules.resolved_act_copy(local.id).is_none());
    }

    #[test]
    fn registers_act_body_as_companion_module_operations_and_methods() {
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
        let operation = lower.modules.value_decls(companion, &Name("say".into()));
        assert_eq!(operation.len(), 1);
        assert!(lower.modules.is_act_operation_def(operation[0].def));
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
