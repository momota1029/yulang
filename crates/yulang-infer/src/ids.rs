use std::cell::Cell;

use serde::{Deserialize, Serialize};

/// 変数・関数・型などの定義を一意に識別する ID。
/// 定義ひとつにつき必ずひとつ発行される。
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct DefId(pub u32);

// LowerState は単一スレッド内で作って解く graph として扱う。
// 別テストの lowering と DefId/TypeVar の列が混ざると、state 内の
// snapshot remap 前提が崩れるため、発行カウンタは thread-local にする。
thread_local! {
    static NEXT_DEF_ID: Cell<u32> = const { Cell::new(0) };
    static NEXT_REF_ID: Cell<u32> = const { Cell::new(0) };
    static NEXT_TYPE_VAR: Cell<u32> = const { Cell::new(0) };
}

pub fn fresh_def_id() -> DefId {
    DefId(fresh_u32(&NEXT_DEF_ID))
}

/// 変数の参照（use site）を一意に識別する ID。
/// lowering 時に fresh な TypeVar とともに発行される。
/// どの DefId を参照しているかは RefTable に記録される。
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct RefId(pub u32);

pub fn fresh_ref_id() -> RefId {
    RefId(fresh_u32(&NEXT_REF_ID))
}

/// 型変数。制約テーブルを引くまで実際の型は不明。
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct TypeVar(pub u32);

pub fn fresh_type_var() -> TypeVar {
    TypeVar(fresh_u32(&NEXT_TYPE_VAR))
}

pub fn fresh_frozen_type_var() -> TypeVar {
    TypeVar(fresh_u32(&NEXT_TYPE_VAR))
}

pub(crate) fn reserve_type_vars_through(max: TypeVar) {
    let next = max.0.saturating_add(1);
    NEXT_TYPE_VAR.with(|counter| {
        if counter.get() < next {
            counter.set(next);
        }
    });
}

fn fresh_u32(counter: &'static std::thread::LocalKey<Cell<u32>>) -> u32 {
    counter.with(|counter| {
        let id = counter.get();
        counter.set(id.saturating_add(1));
        id
    })
}

/// TypeArena 内の Pos ノードへのインデックス。
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct PosId(pub u32);

/// TypeArena 内の Neg ノードへのインデックス。
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct NegId(pub u32);

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn fresh_ids_are_thread_local() {
        let main_def = fresh_def_id();
        let main_ref = fresh_ref_id();
        let main_type = fresh_type_var();

        std::thread::spawn(|| {
            for _ in 0..10_000 {
                let _ = fresh_def_id();
                let _ = fresh_ref_id();
                let _ = fresh_type_var();
            }
        })
        .join()
        .unwrap();

        assert_eq!(fresh_def_id().0, main_def.0 + 1);
        assert_eq!(fresh_ref_id().0, main_ref.0 + 1);
        assert_eq!(fresh_type_var().0, main_type.0 + 1);
    }
}
