//! pass2 で型注釈 CST を、解決済みの小さな注釈型へ読む。
//!
//! 注釈は推論済みの型そのものではない。ここでは pass1 が作った `ModuleTable` と
//! pass2 の `module` / `site` を使い、surface の型名を builtin / 型宣言 ID に解決する。
//! 後続の制約生成は、この `AnnType` を必要な polarity に応じて `Pos` / `Neg` へ落とす。

mod builder;
mod constraints;
#[cfg(test)]
mod tests;

use parser::lex::SyntaxKind;
use parser::sink::YulangLanguage;
use poly::types::{
    BuiltinType, Neg, NegId, Neu, NeuId, Pos, PosId, StackWeight, SubtractId, Subtractability,
    TypeVar,
};
use rowan::{NodeOrToken, SyntaxNode};
use rustc_hash::{FxHashMap, FxHashSet};
use sources::Name;

use crate::{
    Arena as InferArena, ModuleId, ModuleOrder, ModuleTable, ModuleTypeKind, TypeDeclId,
    constraints::TypeLevel,
};

pub use builder::{AnnTypeBuilder, build_ann_type_expr};
pub(crate) use builder::{args_from_ann, effect_row_has_wildcard};
pub use constraints::AnnConstraintLowerer;

type Cst = SyntaxNode<YulangLanguage>;
type CstItem = NodeOrToken<Cst, rowan::SyntaxToken<YulangLanguage>>;

#[derive(Debug, Clone, PartialEq, Eq)]
/// 型注釈として読んだ値。
///
/// `AnnType` は pass2 で名前解決済みの注釈値で、constraint graph の型 node ではない。
pub enum AnnType {
    Builtin(BuiltinType),
    Named(TypeDeclId),
    Var(AnnTypeVar),
    Wildcard(AnnTypeVar),
    EffectRow(AnnEffectRow),
    Effectful {
        eff: AnnEffectRow,
        ret: Box<AnnType>,
    },
    Tuple(Vec<AnnType>),
    Apply {
        callee: Box<AnnType>,
        args: Vec<AnnType>,
    },
    Function {
        param: Box<AnnType>,
        arg_eff: Option<AnnEffectRow>,
        ret_eff: Option<AnnEffectRow>,
        ret: Box<AnnType>,
    },
}

#[derive(Debug, Clone, PartialEq, Eq)]
/// effect row 注釈。
///
/// `[io; 'e]` は items に `io`、tail に `'e` を持つ。`['e]` は tail だけの row として扱う。
pub struct AnnEffectRow {
    pub items: Vec<AnnEffectAtom>,
    pub tail: Option<AnnTypeVar>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
/// effect row 内の atom。
///
/// `_` は effect row の wildcard として、具体型名とは別に保持する。
pub enum AnnEffectAtom {
    Type(AnnType),
    Wildcard,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
/// annotation scope 内の型変数 identity。
pub struct AnnTypeVarId(pub u32);

#[derive(Debug, Clone, PartialEq, Eq)]
/// 型注釈内の型変数。
///
/// `id` は annotation scope 内だけで意味を持つ。同じ scope の同名 var は同じ `id` を共有する。
pub struct AnnTypeVar {
    pub id: AnnTypeVarId,
    pub name: String,
}

#[derive(Debug, Clone, PartialEq, Eq)]
/// type `with` body の中だけで有効な `self` 型 alias。
///
/// `self` は annotation builder ごとに、その builder の型変数 scope を使って
/// `owner 'a 'b ...` へ展開される。
pub struct AnnSelfAlias {
    pub owner: TypeDeclId,
    pub type_vars: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
/// 注釈 builder が構造化して返す失敗。
pub enum AnnBuildError {
    ExpectedTypeExpr { kind: SyntaxKind },
    EmptyTypeExpr,
    EmptyEffectfulType,
    MissingFunctionReturn,
    MissingEffectRow,
    InvalidEffectRowTail { ty: AnnType },
    UnresolvedTypeName { path: Vec<Name> },
    UnsupportedSyntax { kind: SyntaxKind },
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
/// 注釈を接続する対象 computation。
pub struct AnnComputationTarget {
    pub value: TypeVar,
    pub effect: TypeVar,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AnnComputationConnection {
    pub subtracts: Vec<SubtractId>,
    pub effect_stack: Option<AnnEffectStackConnection>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AnnEffectStackConnection {
    pub inner: TypeVar,
    pub arg_eff: NegId,
    pub weight: StackWeight,
    pub subtracts: Vec<SubtractId>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
/// annotation constraint lowering の失敗。
pub enum AnnConstraintError {
    MissingTypeDecl { id: TypeDeclId },
    InvalidConstructorCallee { ty: AnnType },
    InvalidEffectAtom { ty: AnnType },
    WildcardEffectRowInTypePosition,
}
