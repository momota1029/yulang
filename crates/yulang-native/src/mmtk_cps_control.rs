//! MMTk-specialized CPS control helpers.
//!
//! This module is the start of the non-mirroring control path. The existing
//! `runtime_i64` path stores closures, thunks, and resumptions as Rust structs.
//! These helpers store the control object itself as an MMTk `YValue` object and
//! decode the code word/env slots from the MMTk payload when applying/forcing.

use std::cell::RefCell;
use std::collections::HashMap;

use cranelift_jit::JITBuilder;

use crate::gc_runtime::{YObjectKind, YValue};
use crate::mmtk_runtime::mmtk_cps_context_ptr;

type MmtkCpsClosureEntry = extern "C" fn(*const i64, i64) -> i64;
type MmtkCpsThunkEntry = extern "C" fn(*const i64) -> i64;

thread_local! {
    static MMTK_CPS_CONTROL_THUNK_SIDECARS: RefCell<HashMap<i64, usize>> = RefCell::new(HashMap::new());
}

unsafe extern "C" {
    fn yulang_cps_control_capture_context_is_empty_i64() -> i64;
    fn yulang_cps_is_applicable_i64(value: usize) -> i64;
    fn yulang_cps_abort_active_i64() -> i64;
    fn yulang_cps_scope_return_active_i64() -> i64;
    fn yulang_cps_make_closure_i64_0(code: usize) -> usize;
    fn yulang_cps_make_closure_i64_1(code: usize, a: i64) -> usize;
    fn yulang_cps_make_closure_i64_2(code: usize, a: i64, b: i64) -> usize;
    fn yulang_cps_make_closure_i64_3(code: usize, a: i64, b: i64, c: i64) -> usize;
    fn yulang_cps_make_closure_i64_4(code: usize, a: i64, b: i64, c: i64, d: i64) -> usize;
    fn yulang_cps_make_closure_i64_many(code: usize, ptr: *const i64, len: i64) -> usize;
    fn yulang_cps_make_thunk_i64_0(code: usize) -> usize;
    fn yulang_cps_make_thunk_i64_1(code: usize, a: i64) -> usize;
    fn yulang_cps_make_thunk_i64_2(code: usize, a: i64, b: i64) -> usize;
    fn yulang_cps_make_thunk_i64_3(code: usize, a: i64, b: i64, c: i64) -> usize;
    fn yulang_cps_make_thunk_i64_4(code: usize, a: i64, b: i64, c: i64, d: i64) -> usize;
    fn yulang_cps_make_thunk_i64_many(code: usize, ptr: *const i64, len: i64) -> usize;
    fn yulang_cps_is_thunk_i64(value: i64) -> i64;
    #[cfg(test)]
    fn yulang_cps_fresh_guard_i64() -> i64;
    fn yulang_cps_add_thunk_boundary_i64(
        value: usize,
        guard_id: i64,
        allowed_mask: i64,
        active: i64,
    ) -> usize;
    fn yulang_cps_add_empty_context_thunk_boundary_i64(
        code: usize,
        env_ptr: *const i64,
        env_len: i64,
        guard_id: i64,
        allowed_mask: i64,
        active: i64,
    ) -> usize;
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
        yulang_mmtk_cps_control_add_thunk_boundary_i64,
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

pub(crate) fn reset_mmtk_cps_control_state() {
    MMTK_CPS_CONTROL_THUNK_SIDECARS.with(|sidecars| sidecars.borrow_mut().clear());
}

pub(crate) fn is_mmtk_cps_control_thunk_value(value: i64) -> bool {
    is_compact_control_kind(value, YObjectKind::Thunk)
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
        if native_cps_non_local_flow_active() {
            return value;
        }
        if unsafe { yulang_cps_is_applicable_i64(value as usize) } == 1 {
            let result = unsafe { yulang_cps_apply_closure_i64(value as usize, arg) };
            return yulang_mmtk_cps_control_force_thunk_i64(result);
        }
        eprintln!("MMTk CPS control apply received a non-applicable control value: {value:#x}");
        std::process::abort();
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
pub extern "C" fn yulang_mmtk_cps_control_add_thunk_boundary_i64(
    value: i64,
    guard_id: i64,
    allowed_mask: i64,
    active: i64,
) -> i64 {
    let native_thunk =
        if let Some((code, env)) = compact_control_entry_parts(value, YObjectKind::Thunk) {
            if let Some(native_thunk) = compact_thunk_sidecar(value) {
                return unsafe {
                    yulang_cps_add_thunk_boundary_i64(native_thunk, guard_id, allowed_mask, active)
                        as i64
                };
            }
            return unsafe {
                yulang_cps_add_empty_context_thunk_boundary_i64(
                    code as usize,
                    env,
                    compact_control_env_len(value).unwrap_or(0) as i64,
                    guard_id,
                    allowed_mask,
                    active,
                ) as i64
            };
        } else {
            value as usize
        };
    unsafe {
        yulang_cps_add_thunk_boundary_i64(native_thunk, guard_id, allowed_mask, active) as i64
    }
}

#[unsafe(no_mangle)]
pub extern "C" fn yulang_mmtk_cps_control_is_thunk_i64(value: i64) -> i64 {
    if is_compact_control_kind(value, YObjectKind::Thunk) {
        1
    } else {
        unsafe { yulang_cps_is_thunk_i64(value) }
    }
}

#[unsafe(no_mangle)]
pub extern "C" fn yulang_mmtk_cps_control_force_thunk_i64(value: i64) -> i64 {
    let mut value = value;
    let mut forced = false;
    while let Some((code, env)) = compact_control_entry_parts(value, YObjectKind::Thunk) {
        forced = true;
        if let Some(native_thunk) = compact_thunk_sidecar(value) {
            if mmtk_cps_control_trace_enabled() {
                eprintln!("[MMTK-CPS] force_sidecar: compact={value:#x} native={native_thunk:#x}");
            }
            return unsafe { yulang_cps_force_thunk_i64(native_thunk) };
        }
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
    if !compact_control_can_capture_current_context() {
        return native_make_closure(code, env);
    }
    let Some(context) = mmtk_control_context_mut() else {
        return native_make_closure(code, env);
    };
    context
        .context_mut()
        .heap_mut()
        .allocate_compact_closure_i64(code, env)
        .raw() as i64
}

fn make_thunk(code: usize, env: &[i64]) -> i64 {
    if !compact_control_can_capture_current_context() && !compact_thunk_sidecars_enabled() {
        return native_make_thunk(code, env);
    }
    let Some(context) = mmtk_control_context_mut() else {
        return native_make_thunk(code, env);
    };
    let thunk = context
        .context_mut()
        .heap_mut()
        .allocate_compact_thunk_i64(code, env)
        .raw() as i64;
    if !compact_control_can_capture_current_context() {
        let native_thunk = native_make_thunk(code, env) as usize;
        if mmtk_cps_control_trace_enabled() {
            eprintln!("[MMTK-CPS] make_sidecar: compact={thunk:#x} native={native_thunk:#x}");
        }
        remember_compact_thunk_sidecar(thunk, native_thunk);
    }
    thunk
}

fn make_resumption(code: usize, env: &[i64]) -> i64 {
    let Some(context) = mmtk_control_context_mut() else {
        return 0;
    };
    context
        .context_mut()
        .heap_mut()
        .allocate_compact_resumption_i64(code, env)
        .raw() as i64
}

fn compact_control_can_capture_current_context() -> bool {
    (unsafe { yulang_cps_control_capture_context_is_empty_i64() }) == 1
}

fn native_cps_non_local_flow_active() -> bool {
    unsafe { yulang_cps_abort_active_i64() != 0 || yulang_cps_scope_return_active_i64() != 0 }
}

fn compact_thunk_sidecars_enabled() -> bool {
    std::env::var_os("YULANG_MMTK_CPS_CONTROL_THUNK_SIDECARS")
        .is_some_and(|value| value == "unsafe")
}

fn mmtk_cps_control_trace_enabled() -> bool {
    std::env::var_os("YULANG_MMTK_CPS_CONTROL_TRACE").is_some_and(|value| value == "1")
}

fn remember_compact_thunk_sidecar(value: i64, native_thunk: usize) {
    MMTK_CPS_CONTROL_THUNK_SIDECARS.with(|sidecars| {
        sidecars.borrow_mut().insert(value, native_thunk);
    });
}

fn compact_thunk_sidecar(value: i64) -> Option<usize> {
    MMTK_CPS_CONTROL_THUNK_SIDECARS.with(|sidecars| sidecars.borrow().get(&value).copied())
}

fn native_make_closure(code: usize, env: &[i64]) -> i64 {
    unsafe {
        (match env {
            [] => yulang_cps_make_closure_i64_0(code),
            [a] => yulang_cps_make_closure_i64_1(code, *a),
            [a, b] => yulang_cps_make_closure_i64_2(code, *a, *b),
            [a, b, c] => yulang_cps_make_closure_i64_3(code, *a, *b, *c),
            [a, b, c, d] => yulang_cps_make_closure_i64_4(code, *a, *b, *c, *d),
            _ => yulang_cps_make_closure_i64_many(code, env.as_ptr(), env.len() as i64),
        }) as i64
    }
}

fn native_make_thunk(code: usize, env: &[i64]) -> i64 {
    unsafe {
        (match env {
            [] => yulang_cps_make_thunk_i64_0(code),
            [a] => yulang_cps_make_thunk_i64_1(code, *a),
            [a, b] => yulang_cps_make_thunk_i64_2(code, *a, *b),
            [a, b, c] => yulang_cps_make_thunk_i64_3(code, *a, *b, *c),
            [a, b, c, d] => yulang_cps_make_thunk_i64_4(code, *a, *b, *c, *d),
            _ => yulang_cps_make_thunk_i64_many(code, env.as_ptr(), env.len() as i64),
        }) as i64
    }
}

fn compact_control_entry_parts(value: i64, kind: YObjectKind) -> Option<(u64, *const i64)> {
    let value = YValue::from_raw(value as usize);
    mmtk_control_context_mut()?
        .context()
        .heap()
        .compact_control_entry_parts(value, kind)
}

fn compact_control_env_len(value: i64) -> Option<usize> {
    let value = YValue::from_raw(value as usize);
    mmtk_control_context_mut()?
        .context()
        .heap()
        .compact_control_env_len(value)
}

fn is_compact_control_kind(value: i64, kind: YObjectKind) -> bool {
    let Some(context) = mmtk_control_context_mut() else {
        return false;
    };
    let value = YValue::from_raw(value as usize);
    context.context().heap().is_tracked_object_kind(value, kind)
}

fn mmtk_control_context_mut() -> Option<&'static mut crate::mmtk_runtime::MmtkNativeRuntimeContext>
{
    mmtk_cps_context_ptr().map(|ptr| unsafe { &mut *ptr })
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

    #[test]
    fn native_cps_force_recognizes_mmtk_compact_thunks() {
        let _guard = mmtk_test_lock();
        yulang_mmtk_cps_reset_i64();

        let thunk = yulang_mmtk_cps_control_make_thunk_i64_1(thunk_value as *const () as usize, 99);
        assert_eq!(unsafe { yulang_cps_is_thunk_i64(thunk) }, 1);
        assert_eq!(unsafe { yulang_cps_force_thunk_i64(thunk as usize) }, 99);
    }

    #[test]
    fn mmtk_cps_control_thunk_boundary_uses_empty_capture_context() {
        let _guard = mmtk_test_lock();
        yulang_mmtk_cps_reset_i64();

        let thunk = yulang_mmtk_cps_control_make_thunk_i64_1(thunk_value as *const () as usize, 99);
        let bounded = yulang_mmtk_cps_control_add_thunk_boundary_i64(thunk, 1, i64::MAX, 1);
        assert_eq!(yulang_mmtk_cps_control_is_thunk_i64(bounded), 1);
        assert_eq!(yulang_mmtk_cps_control_force_thunk_i64(bounded), 99);
    }

    #[test]
    fn mmtk_cps_control_thunk_sidecar_preserves_non_empty_capture_context() {
        let _guard = mmtk_test_lock();
        unsafe {
            std::env::set_var("YULANG_MMTK_CPS_CONTROL_THUNK_SIDECARS", "unsafe");
        }
        yulang_mmtk_cps_reset_i64();

        unsafe {
            yulang_cps_fresh_guard_i64();
        }
        assert_eq!(
            unsafe { yulang_cps_control_capture_context_is_empty_i64() },
            0
        );
        let thunk = yulang_mmtk_cps_control_make_thunk_i64_1(thunk_value as *const () as usize, 99);
        assert_eq!(yulang_mmtk_cps_control_is_thunk_i64(thunk), 1);
        assert!(is_compact_control_kind(thunk, YObjectKind::Thunk));
        assert!(compact_thunk_sidecar(thunk).is_some());
        assert_eq!(yulang_mmtk_cps_control_force_thunk_i64(thunk), 99);
        unsafe {
            std::env::remove_var("YULANG_MMTK_CPS_CONTROL_THUNK_SIDECARS");
        }
    }
}
