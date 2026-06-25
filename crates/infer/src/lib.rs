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
pub mod check;
pub mod compact;
mod compiled_lowering;
mod compiled_namespace;
mod compiled_runtime;
mod compiled_typed;
pub mod constraints;
pub mod dump;
pub mod generalize;
pub mod instantiate;
pub mod lowering;
pub mod methods;
mod module_map;
mod module_table;
pub mod patterns;
mod role_solve;
pub mod roles;
pub mod scc;
mod std_paths;
mod syntax;
#[cfg(test)]
mod tests_root;
mod time;
pub mod typing;
pub mod uses;

pub use arena::Arena;
pub use compiled_lowering::*;
pub use compiled_namespace::*;
pub use compiled_runtime::*;
pub use compiled_typed::*;
pub(crate) use module_map::{
    LoadedFileCsts, append_root_loaded_file_to_lower, lower_loaded_file_csts_module_map,
};
pub use module_map::{LoadedFilesError, lower_loaded_files_module_map, lower_module_map};
pub(crate) use syntax::*;

use crate::act_resolve::{ActTypeExpr, ActTypeResolver};
use parser::lex::SyntaxKind;
use parser::sink::YulangLanguage;
use poly::dump::DumpLabels;
use poly::expr::{Arena as PolyArena, Def, DefId, Vis};
use rowan::{NodeOrToken, SyntaxNode};
use rustc_hash::{FxHashMap, FxHashSet};
use serde::{Deserialize, Serialize};
use sources::{LoadedFile, Name, Path as ModulePath, SourceRange, UseImport};
use std::fmt;

type Cst = SyntaxNode<YulangLanguage>;

fn module_path_site() -> ModuleOrder {
    ModuleOrder::from_index(u32::MAX)
}

// ── モジュールツリー（infer 作業用。名前解決が済めば poly には残さない）──────

/// pass1 / pass2 の作業用 module ID。
///
/// `poly` の最終 IR へは残さない。名前解決中に「今どの module scope にいるか」を持つための
/// infer-local な ID。
#[derive(Clone, Copy, PartialEq, Eq, Debug, Hash, Serialize, Deserialize)]
pub struct ModuleId(usize);

/// module 内の宣言位置。
///
/// 同じ module の中で、宣言が source 上のどの順に現れたかを表す。
/// resolver はこの order を基準に「上に同名宣言があれば最後、なければ下の直近」を選ぶ。
/// binding body は header の後を解決しているので、同じ order の宣言も既に見えているものとして扱う。
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Debug, Hash, Serialize, Deserialize)]
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

#[derive(Clone)]
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

#[derive(Clone, Copy, PartialEq, Eq, Debug, Hash, Serialize, Deserialize)]
struct ModuleDeclId(usize);

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SourceSpan {
    pub file: ModulePath,
    pub range: SourceRange,
}

#[derive(Clone, Copy, PartialEq, Eq, Debug, Hash, Serialize, Deserialize)]
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

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct ConstructorDecl {
    pub owner: TypeDeclId,
    pub module: ModuleId,
    pub type_vars: Vec<String>,
    pub payload: ConstructorPayload,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct ErrorDecl {
    pub owner: TypeDeclId,
    pub module: ModuleId,
    pub companion: ModuleId,
    pub type_vars: Vec<String>,
    pub vis: Vis,
    pub variants: Vec<ErrorVariantDecl>,
    pub wrap_def: Option<DefId>,
    pub up_def: Option<DefId>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct ErrorVariantDecl {
    pub name: Name,
    pub constructor_def: DefId,
    pub operation_def: DefId,
    pub payload: ConstructorPayload,
    pub from: bool,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum ConstructorPayload {
    Unit,
    Tuple(Vec<ConstructorPayloadItem>),
    Record(Vec<ConstructorRecordPayloadField>),
}

impl ConstructorPayload {
    fn from_struct(node: &Cst) -> Self {
        let fields = crate::struct_field_nodes(node);
        payload_from_fields(fields)
    }

    fn from_enum_variant(node: &Cst) -> Self {
        let fields = crate::enum_variant_field_nodes(node);
        if !fields.is_empty() {
            return payload_from_fields(fields);
        }
        let items = crate::enum_variant_direct_type_exprs(node)
            .into_iter()
            .map(|ty| ConstructorPayloadItem {
                ty: Some(StoredSignature::source(ty)),
            })
            .collect::<Vec<_>>();
        if items.is_empty() {
            Self::Unit
        } else {
            Self::Tuple(items)
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct ConstructorPayloadItem {
    pub ty: Option<StoredSignature>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct ConstructorRecordPayloadField {
    pub name: Name,
    pub ty: Option<StoredSignature>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum StoredSignature {
    Source(Cst),
    Lowered(lowering::SignatureType),
}

impl StoredSignature {
    fn source(node: Cst) -> Self {
        Self::Source(node)
    }

    pub fn lowered(signature: lowering::SignatureType) -> Self {
        Self::Lowered(signature)
    }
}

fn payload_from_fields(fields: Vec<Cst>) -> ConstructorPayload {
    if fields.is_empty() {
        return ConstructorPayload::Unit;
    }

    let mut record = Vec::new();
    let mut tuple = Vec::new();
    for field in fields {
        if let Some(name) = crate::struct_field_name(&field) {
            record.push(ConstructorRecordPayloadField {
                name,
                ty: crate::field_type_expr(&field).map(StoredSignature::source),
            });
        } else {
            tuple.push(ConstructorPayloadItem {
                ty: crate::field_type_expr(&field).map(StoredSignature::source),
            });
        }
    }

    if !record.is_empty() {
        ConstructorPayload::Record(record)
    } else {
        ConstructorPayload::Tuple(tuple)
    }
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
    pub signature: Option<StoredSignature>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct ActOperationSig {
    name: Name,
    signature: Option<StoredSignature>,
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
    pub signature: Option<StoredSignature>,
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

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct CastDecl {
    pub def: DefId,
    pub module: ModuleId,
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

/// module import view に入った値宣言を外へ見せるための summary。
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ModuleImportedValueDecl {
    pub name: Name,
    pub vis: Vis,
    pub order: ModuleOrder,
    pub def: DefId,
}

/// module import view に入った型宣言を外へ見せるための summary。
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ModuleImportedTypeDecl {
    pub name: Name,
    pub vis: Vis,
    pub order: ModuleOrder,
    pub decl: ModuleTypeDecl,
}

/// module import view に入った子 module 宣言を外へ見せるための summary。
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ModuleImportedModuleDecl {
    pub name: Name,
    pub vis: Vis,
    pub order: ModuleOrder,
    pub module: ModuleId,
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(crate) struct ModulePathTarget {
    pub module: ModuleId,
    pub def: Option<DefId>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
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
    /// この import を作った alias（use 文）の visibility。`pub use` の entry だけが
    /// 外の module から再エクスポートとして見える。
    vis: Vis,
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct ImportedTypeDecl {
    order: ModuleOrder,
    decl: ModuleTypeDecl,
    vis: Vis,
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct ImportedModuleDecl {
    order: ModuleOrder,
    module: ModuleId,
    vis: Vis,
}

#[derive(Clone)]
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
#[derive(Clone)]
pub struct ModuleTable {
    nodes: Vec<ModuleNode>,
    act_templates: FxHashMap<TypeDeclId, Cst>,
    act_type_vars: FxHashMap<TypeDeclId, Vec<String>>,
    act_copies: FxHashMap<TypeDeclId, ActCopyDecl>,
    resolved_act_copies: FxHashMap<TypeDeclId, ResolvedActCopyDecl>,
    synthetic_var_act_copies: FxHashSet<TypeDeclId>,
    synthetic_var_act_uses: FxHashMap<DefId, Vec<SyntheticVarActUse>>,
    synthetic_sub_label_act_copies: FxHashSet<TypeDeclId>,
    synthetic_sub_label_act_uses: FxHashMap<DefId, Vec<SyntheticSubLabelActUse>>,
    root_expr_owners: FxHashMap<ModuleId, Vec<Option<DefId>>>,
    act_ops: FxHashMap<TypeDeclId, Vec<ActOperationSig>>,
    act_op_defs: FxHashMap<DefId, ActOperationDef>,
    lazy_ops: FxHashSet<DefId>,
    act_methods: FxHashMap<TypeDeclId, Vec<ActMethodDecl>>,
    constructors: FxHashMap<DefId, ConstructorDecl>,
    error_decls: FxHashMap<TypeDeclId, ErrorDecl>,
    error_constructor_ops: FxHashMap<DefId, DefId>,
    error_op_constructors: FxHashMap<DefId, DefId>,
    casts: FxHashMap<ModuleId, Vec<CastDecl>>,
    role_inputs: FxHashMap<TypeDeclId, Vec<String>>,
    role_associated: FxHashMap<TypeDeclId, Vec<String>>,
    role_impls: FxHashMap<ModuleId, Vec<RoleImplDecl>>,
    role_methods: FxHashMap<TypeDeclId, Vec<RoleMethodDecl>>,
    type_companions: FxHashMap<TypeDeclId, ModuleId>,
    type_methods: FxHashMap<TypeDeclId, Vec<TypeMethodDecl>>,
    type_field_methods: FxHashMap<TypeDeclId, Vec<TypeFieldMethodDecl>>,
    def_source_spans: FxHashMap<DefId, SourceSpan>,
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

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct SyntheticSubLabelActUse {
    pub label: Name,
    pub act: TypeDeclId,
}

/// pass1 の出力。
///
/// `arena` は DefId と module children を含む薄い `poly` IR、`modules` は pass2 で scope を引くための
/// infer-local table。body と型制約はまだ空のまま残す。
pub struct Lower {
    /// pass1 が採番した `poly` Arena。
    pub arena: PolyArena,
    /// pass2 の名前解決で使う infer-local module map。
    pub modules: ModuleTable,
    source_file: ModulePath,
}
