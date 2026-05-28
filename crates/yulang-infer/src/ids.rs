use std::cell::Cell;
use std::sync::atomic::{AtomicU32, Ordering};

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
    static FRESH_ID_THREAD_BASE: Cell<Option<u32>> = const { Cell::new(None) };
}

static NEXT_FRESH_ID_SCOPE_BASE: AtomicU32 = AtomicU32::new(0);
const FRESH_ID_SCOPE_BLOCK: u32 = 100_000;

pub(crate) fn with_fresh_id_scope<T>(f: impl FnOnce() -> T) -> T {
    let base = fresh_id_thread_base();
    set_fresh_id_counters(base, base, 0);
    f()
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

pub(crate) fn reserve_def_ids_through(max: DefId) {
    reserve_counter_through(&NEXT_DEF_ID, max.0);
}

pub(crate) fn reserve_ref_ids_through(max: RefId) {
    reserve_counter_through(&NEXT_REF_ID, max.0);
}

pub(crate) fn reserve_type_vars_through(max: TypeVar) {
    reserve_counter_through(&NEXT_TYPE_VAR, max.0);
}

fn fresh_u32(counter: &'static std::thread::LocalKey<Cell<u32>>) -> u32 {
    counter.with(|counter| {
        let id = counter.get();
        counter.set(id.saturating_add(1));
        id
    })
}

fn reserve_counter_through(counter: &'static std::thread::LocalKey<Cell<u32>>, max: u32) {
    let next = max.saturating_add(1);
    counter.with(|counter| {
        if counter.get() < next {
            counter.set(next);
        }
    });
}

fn set_fresh_id_counters(next_def_id: u32, next_ref_id: u32, next_type_var: u32) {
    NEXT_DEF_ID.with(|counter| counter.set(next_def_id));
    NEXT_REF_ID.with(|counter| counter.set(next_ref_id));
    NEXT_TYPE_VAR.with(|counter| counter.set(next_type_var));
}

fn fresh_id_thread_base() -> u32 {
    FRESH_ID_THREAD_BASE.with(|slot| {
        if let Some(base) = slot.get() {
            return base;
        }
        let base = NEXT_FRESH_ID_SCOPE_BASE.fetch_add(FRESH_ID_SCOPE_BLOCK, Ordering::Relaxed);
        slot.set(Some(base));
        base
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
