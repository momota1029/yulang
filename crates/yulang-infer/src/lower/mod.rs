//! CST → TIR の lowering ワンパス。
//!
//! このモジュールがやること：
//! - ModuleTable にモジュール・変数・型を登録する
//! - 全ノードに fresh な TypeVar を振る（tv, eff）
//! - アノテーションがあれば制約として Infer に登録する
//! - その場で確定できる型制約を Infer に流す
//! - RefTable に RefId → DefId の対応を記録する（解決できないものは unresolved）
pub mod ann;
pub mod builtin_types;
pub mod ctx;
pub mod expr;
pub mod primitives;
pub mod profile;
pub mod role;
mod role_finalize;
pub mod signature;
pub mod state;
pub mod state_types;
pub mod stmt;
pub mod where_clause;

use rowan::SyntaxNode as RowanNode;
use yulang_parser::sink::YulangLanguage;

pub type SyntaxNode = RowanNode<YulangLanguage>;

pub use profile::{FinalizeCompactProfile, FinalizeCompactResults, LowerDetailProfile};
pub use state::LowerState;
pub use state_types::{
    ActiveRecursiveSelfInstance, EnumVariantPatternShape, FunctionSigEffectHint,
};
