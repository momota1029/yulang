use std::sync::atomic::{AtomicU32, Ordering};

/// 変数・関数・型などの定義を一意に識別する ID。
/// 定義ひとつにつき必ずひとつ発行される。
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct DefId(pub u32);

static NEXT_DEF_ID: AtomicU32 = AtomicU32::new(0);

pub fn fresh_def_id() -> DefId {
    DefId(NEXT_DEF_ID.fetch_add(1, Ordering::Relaxed))
}

/// 変数の参照（use site）を一意に識別する ID。
/// lowering 時に fresh な TypeVar とともに発行される。
/// どの DefId を参照しているかは RefTable に記録される。
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct RefId(pub u32);

static NEXT_REF_ID: AtomicU32 = AtomicU32::new(0);

pub fn fresh_ref_id() -> RefId {
    RefId(NEXT_REF_ID.fetch_add(1, Ordering::Relaxed))
}

/// 型変数。制約テーブルを引くまで実際の型は不明。
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct TypeVar(pub u32);

static NEXT_TYPE_VAR: AtomicU32 = AtomicU32::new(0);

pub fn fresh_type_var() -> TypeVar {
    TypeVar(NEXT_TYPE_VAR.fetch_add(1, Ordering::Relaxed))
}

pub fn fresh_frozen_type_var() -> TypeVar {
    TypeVar(NEXT_TYPE_VAR.fetch_add(1, Ordering::Relaxed))
}

/// TypeArena 内の Pos ノードへのインデックス。
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct PosId(pub u32);

/// TypeArena 内の Neg ノードへのインデックス。
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct NegId(pub u32);
