//! MMTk-specialized CPS control helpers.
//!
//! This module is the start of the non-mirroring control path. The existing
//! `runtime_i64` path stores closures, thunks, and resumptions as Rust structs.
//! These helpers store the control object itself as an MMTk `YValue` object and
//! decode the code word/env slots from the MMTk payload when applying/forcing.

use cranelift_jit::JITBuilder;

use crate::gc_runtime::{YObjectKind, YValue};
use crate::mmtk_runtime::with_mmtk_cps_context;

type MmtkCpsClosureEntry = extern "C" fn(*const i64, i64) -> i64;
type MmtkCpsThunkEntry = extern "C" fn(*const i64) -> i64;

unsafe extern "C" {
    fn yulang_cps_apply_closure_i64(value: usize, arg: i64) -> i64;
    fn yulang_cps_force_thunk_i64(value: usize) -> i64;
}

pub fn register_mmtk_cps_control_jit_symbols(builder: &mut JITBuilder) {
    macro_rules! symbols {
        ($($symbol:ident),+ $(,)?) => {
            $(builder.symbol(stringify!($symbol), $symbol as *const u8);)+
        };
    }

    symbols!(
        yulang_mmtk_cps_control_make_closure_i64_0,
        yulang_mmtk_cps_control_make_closure_i64_1,
        yulang_mmtk_cps_control_make_closure_i64_2,
        yulang_mmtk_cps_control_make_closure_i64_3,
        yulang_mmtk_cps_control_make_closure_i64_4,
        yulang_mmtk_cps_control_make_closure_i64_many,
        yulang_mmtk_cps_control_apply_closure_i64,
        yulang_mmtk_cps_control_make_thunk_i64_0,
        yulang_mmtk_cps_control_make_thunk_i64_1,
        yulang_mmtk_cps_control_make_thunk_i64_2,
        yulang_mmtk_cps_control_make_thunk_i64_3,
        yulang_mmtk_cps_control_make_thunk_i64_4,
        yulang_mmtk_cps_control_make_thunk_i64_many,
        yulang_mmtk_cps_control_is_thunk_i64,
        yulang_mmtk_cps_control_force_thunk_i64,
        yulang_mmtk_cps_control_make_resumption_i64_0,
        yulang_mmtk_cps_control_make_resumption_i64_1,
        yulang_mmtk_cps_control_make_resumption_i64_2,
        yulang_mmtk_cps_control_make_resumption_i64_3,
        yulang_mmtk_cps_control_make_resumption_i64_4,
        yulang_mmtk_cps_control_make_resumption_i64_many,
        yulang_mmtk_cps_control_is_resumption_i64,
    );
}

#[unsafe(no_mangle)]
pub extern "C" fn yulang_mmtk_cps_control_make_closure_i64_0(code: usize) -> i64 {
    make_closure(code, &[])
}

#[unsafe(no_mangle)]
pub extern "C" fn yulang_mmtk_cps_control_make_closure_i64_1(code: usize, a: i64) -> i64 {
    make_closure(code, &[a])
}

#[unsafe(no_mangle)]
pub extern "C" fn yulang_mmtk_cps_control_make_closure_i64_2(code: usize, a: i64, b: i64) -> i64 {
    make_closure(code, &[a, b])
}

#[unsafe(no_mangle)]
pub extern "C" fn yulang_mmtk_cps_control_make_closure_i64_3(
    code: usize,
    a: i64,
    b: i64,
    c: i64,
) -> i64 {
    make_closure(code, &[a, b, c])
}

#[unsafe(no_mangle)]
pub extern "C" fn yulang_mmtk_cps_control_make_closure_i64_4(
    code: usize,
    a: i64,
    b: i64,
    c: i64,
    d: i64,
) -> i64 {
    make_closure(code, &[a, b, c, d])
}

#[unsafe(no_mangle)]
pub extern "C" fn yulang_mmtk_cps_control_make_closure_i64_many(
    code: usize,
    ptr: *const i64,
    len: i64,
) -> i64 {
    let env = unsafe { native_i64_slice(ptr, len) };
    make_closure(code, &env)
}

#[unsafe(no_mangle)]
pub extern "C" fn yulang_mmtk_cps_control_apply_closure_i64(value: i64, arg: i64) -> i64 {
    let Some((code, env)) = compact_control_entry_parts(value, YObjectKind::Closure) else {
        return unsafe { yulang_cps_apply_closure_i64(value as usize, arg) };
    };
    let entry: MmtkCpsClosureEntry = unsafe { std::mem::transmute(code as usize) };
    yulang_mmtk_cps_control_force_thunk_i64(entry(env, arg))
}

#[unsafe(no_mangle)]
pub extern "C" fn yulang_mmtk_cps_control_make_thunk_i64_0(code: usize) -> i64 {
    make_thunk(code, &[])
}

#[unsafe(no_mangle)]
pub extern "C" fn yulang_mmtk_cps_control_make_thunk_i64_1(code: usize, a: i64) -> i64 {
    make_thunk(code, &[a])
}

#[unsafe(no_mangle)]
pub extern "C" fn yulang_mmtk_cps_control_make_thunk_i64_2(code: usize, a: i64, b: i64) -> i64 {
    make_thunk(code, &[a, b])
}

#[unsafe(no_mangle)]
pub extern "C" fn yulang_mmtk_cps_control_make_thunk_i64_3(
    code: usize,
    a: i64,
    b: i64,
    c: i64,
) -> i64 {
    make_thunk(code, &[a, b, c])
}

#[unsafe(no_mangle)]
pub extern "C" fn yulang_mmtk_cps_control_make_thunk_i64_4(
    code: usize,
    a: i64,
    b: i64,
    c: i64,
    d: i64,
) -> i64 {
    make_thunk(code, &[a, b, c, d])
}

#[unsafe(no_mangle)]
pub extern "C" fn yulang_mmtk_cps_control_make_thunk_i64_many(
    code: usize,
    ptr: *const i64,
    len: i64,
) -> i64 {
    let env = unsafe { native_i64_slice(ptr, len) };
    make_thunk(code, &env)
}

#[unsafe(no_mangle)]
pub extern "C" fn yulang_mmtk_cps_control_is_thunk_i64(value: i64) -> i64 {
    is_compact_control_kind(value, YObjectKind::Thunk).into()
}

#[unsafe(no_mangle)]
pub extern "C" fn yulang_mmtk_cps_control_force_thunk_i64(value: i64) -> i64 {
    let mut value = value;
    let mut forced = false;
    while let Some((code, env)) = compact_control_entry_parts(value, YObjectKind::Thunk) {
        forced = true;
        let entry: MmtkCpsThunkEntry = unsafe { std::mem::transmute(code as usize) };
        value = entry(env);
    }
    if !forced {
        return unsafe { yulang_cps_force_thunk_i64(value as usize) };
    }
    value
}

#[unsafe(no_mangle)]
pub extern "C" fn yulang_mmtk_cps_control_make_resumption_i64_0(code: usize, _handler: i64) -> i64 {
    make_resumption(code, &[])
}

#[unsafe(no_mangle)]
pub extern "C" fn yulang_mmtk_cps_control_make_resumption_i64_1(
    code: usize,
    _handler: i64,
    a: i64,
) -> i64 {
    make_resumption(code, &[a])
}

#[unsafe(no_mangle)]
pub extern "C" fn yulang_mmtk_cps_control_make_resumption_i64_2(
    code: usize,
    _handler: i64,
    a: i64,
    b: i64,
) -> i64 {
    make_resumption(code, &[a, b])
}

#[unsafe(no_mangle)]
pub extern "C" fn yulang_mmtk_cps_control_make_resumption_i64_3(
    code: usize,
    _handler: i64,
    a: i64,
    b: i64,
    c: i64,
) -> i64 {
    make_resumption(code, &[a, b, c])
}

#[unsafe(no_mangle)]
pub extern "C" fn yulang_mmtk_cps_control_make_resumption_i64_4(
    code: usize,
    _handler: i64,
    a: i64,
    b: i64,
    c: i64,
    d: i64,
) -> i64 {
    make_resumption(code, &[a, b, c, d])
}

#[unsafe(no_mangle)]
pub extern "C" fn yulang_mmtk_cps_control_make_resumption_i64_many(
    code: usize,
    _handler: i64,
    ptr: *const i64,
    len: i64,
) -> i64 {
    let env = unsafe { native_i64_slice(ptr, len) };
    make_resumption(code, &env)
}

#[unsafe(no_mangle)]
pub extern "C" fn yulang_mmtk_cps_control_is_resumption_i64(value: i64) -> i64 {
    is_compact_control_kind(value, YObjectKind::Resumption).into()
}

fn make_closure(code: usize, env: &[i64]) -> i64 {
    with_mmtk_cps_context(|context| {
        context
            .context_mut()
            .heap_mut()
            .allocate_compact_closure_i64(code, env)
            .raw() as i64
    })
    .unwrap_or(0)
}

fn make_thunk(code: usize, env: &[i64]) -> i64 {
    with_mmtk_cps_context(|context| {
        context
            .context_mut()
            .heap_mut()
            .allocate_compact_thunk_i64(code, env)
            .raw() as i64
    })
    .unwrap_or(0)
}

fn make_resumption(code: usize, env: &[i64]) -> i64 {
    with_mmtk_cps_context(|context| {
        context
            .context_mut()
            .heap_mut()
            .allocate_compact_resumption_i64(code, env)
            .raw() as i64
    })
    .unwrap_or(0)
}

fn compact_control_entry_parts(value: i64, kind: YObjectKind) -> Option<(u64, *const i64)> {
    with_mmtk_cps_context(|context| {
        let value = YValue::from_raw(value as usize);
        context
            .context()
            .heap()
            .compact_control_entry_parts(value, kind)
    })
    .flatten()
}

fn is_compact_control_kind(value: i64, kind: YObjectKind) -> bool {
    with_mmtk_cps_context(|context| {
        let value = YValue::from_raw(value as usize);
        context.context().heap().is_tracked_object_kind(value, kind)
    })
    .unwrap_or(false)
}

unsafe fn native_i64_slice(ptr: *const i64, len: i64) -> Vec<i64> {
    if ptr.is_null() || len <= 0 {
        return Vec::new();
    }
    unsafe { std::slice::from_raw_parts(ptr, len as usize) }.to_vec()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::mmtk_runtime::{mmtk_test_lock, yulang_mmtk_cps_reset_i64};

    extern "C" fn add_env(env: *const i64, arg: i64) -> i64 {
        let captured = unsafe { *env };
        captured + arg
    }

    extern "C" fn thunk_value(env: *const i64) -> i64 {
        unsafe { *env }
    }

    #[test]
    fn mmtk_cps_control_closure_is_mmtk_object_body() {
        let _guard = mmtk_test_lock();
        yulang_mmtk_cps_reset_i64();

        let closure = yulang_mmtk_cps_control_make_closure_i64_1(add_env as *const () as usize, 40);
        assert!(closure != 0);
        assert_eq!(yulang_mmtk_cps_control_apply_closure_i64(closure, 2), 42);
    }

    #[test]
    fn mmtk_cps_control_thunk_forces_from_mmtk_object_body() {
        let _guard = mmtk_test_lock();
        yulang_mmtk_cps_reset_i64();

        let thunk = yulang_mmtk_cps_control_make_thunk_i64_1(thunk_value as *const () as usize, 99);
        assert_eq!(yulang_mmtk_cps_control_is_thunk_i64(thunk), 1);
        assert_eq!(yulang_mmtk_cps_control_force_thunk_i64(thunk), 99);
    }
}
