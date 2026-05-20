//! MMTk-specialized CPS control helpers.
//!
//! This module is the start of the non-mirroring control path. The existing
//! `runtime_i64` path stores closures, thunks, and resumptions as Rust structs.
//! These helpers store the control object itself as an MMTk `YValue` object and
//! decode the code word/env slots from the MMTk payload when applying/forcing.

use std::cell::RefCell;
use std::sync::atomic::{AtomicU8, Ordering};

use cranelift_jit::JITBuilder;
use rustc_hash::FxHashMap;

use crate::gc_runtime::{YObjectKind, YValue};
use crate::mmtk_runtime::mmtk_cps_context_ptr;

type MmtkCpsClosureEntry = extern "C" fn(*const i64, i64) -> i64;
type MmtkCpsThunkEntry = extern "C" fn(*const i64) -> i64;

thread_local! {
    static MMTK_CPS_CONTROL_ENTRIES: RefCell<FxHashMap<i64, CompactControlEntry>> = RefCell::new(FxHashMap::default());
    static MMTK_CPS_CONTROL_THUNK_SIDECARS: RefCell<FxHashMap<i64, usize>> = RefCell::new(FxHashMap::default());
    static MMTK_CPS_CONTROL_THUNK_CONTEXTS: RefCell<FxHashMap<i64, usize>> = RefCell::new(FxHashMap::default());
}

static COMPACT_THUNK_SIDECARS_ENABLED: AtomicU8 = AtomicU8::new(0);
static COMPACT_THUNK_CONTEXTS_ENABLED: AtomicU8 = AtomicU8::new(0);

unsafe extern "C" {
    #[cfg(test)]
    fn yulang_cps_control_capture_context_is_empty_i64() -> i64;
    fn yulang_cps_control_capture_context_flags_i64() -> i64;
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
    fn yulang_cps_capture_thunk_context_i64() -> usize;
    fn yulang_cps_thunk_context_add_boundary_i64(
        context: usize,
        guard_id: i64,
        allowed_mask: i64,
        active: i64,
    ) -> usize;
    fn yulang_cps_force_thunk_context_i64(
        value: usize,
        context: usize,
        code: usize,
        env_ptr: *const i64,
    ) -> i64;
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

#[cfg(test)]
const CONTROL_CAPTURE_HANDLER_STACK: i64 = 1 << 0;
#[cfg(test)]
const CONTROL_CAPTURE_GUARD_STACK: i64 = 1 << 1;
#[cfg(test)]
const CONTROL_CAPTURE_ACTIVE_BLOCKED: i64 = 1 << 2;
const CONTROL_CAPTURE_PENDING_HANDLER_ENVS: i64 = 1 << 3;
const CONTROL_CAPTURE_PENDING_ESCAPE_TARGETS: i64 = 1 << 4;
const CONTROL_CAPTURE_RESUME_WITH_HANDLER_SIBLINGS: i64 = 1 << 5;
const CONTROL_CAPTURE_ABORT: i64 = 1 << 6;
const CONTROL_CAPTURE_SCOPE_RETURN: i64 = 1 << 7;
const CONTROL_CAPTURE_NON_LOCAL_FLOW: i64 = CONTROL_CAPTURE_ABORT | CONTROL_CAPTURE_SCOPE_RETURN;
const CONTROL_CAPTURE_CLOSURE_UNSAFE: i64 = CONTROL_CAPTURE_PENDING_HANDLER_ENVS
    | CONTROL_CAPTURE_PENDING_ESCAPE_TARGETS
    | CONTROL_CAPTURE_RESUME_WITH_HANDLER_SIBLINGS
    | CONTROL_CAPTURE_NON_LOCAL_FLOW;

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
    MMTK_CPS_CONTROL_ENTRIES.with(|entries| entries.borrow_mut().clear());
    MMTK_CPS_CONTROL_THUNK_SIDECARS.with(|sidecars| sidecars.borrow_mut().clear());
    MMTK_CPS_CONTROL_THUNK_CONTEXTS.with(|contexts| contexts.borrow_mut().clear());
    COMPACT_THUNK_SIDECARS_ENABLED.store(0, Ordering::Relaxed);
    COMPACT_THUNK_CONTEXTS_ENABLED.store(0, Ordering::Relaxed);
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
    let native_thunk = if let Some((code, env)) =
        compact_control_entry_parts(value, YObjectKind::Thunk)
    {
        if let Some(native_thunk) = compact_thunk_sidecar(value) {
            return unsafe {
                yulang_cps_add_thunk_boundary_i64(native_thunk, guard_id, allowed_mask, active)
                    as i64
            };
        }
        if let Some(context) = compact_thunk_context(value) {
            let bounded_context = unsafe {
                yulang_cps_thunk_context_add_boundary_i64(context, guard_id, allowed_mask, active)
            };
            return make_compact_thunk_with_context(
                code as usize,
                env,
                compact_control_env_len(value).unwrap_or(0),
                bounded_context,
            );
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
        if let Some(context) = compact_thunk_context(value) {
            return unsafe {
                yulang_cps_force_thunk_context_i64(value as usize, context, code as usize, env)
            };
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
    let capture = compact_control_capture_state();
    if capture.has_closure_unsafe_state() {
        if mmtk_cps_control_trace_enabled() {
            eprintln!(
                "[MMTK-CPS] make_closure_fallback: flags={:#x}",
                capture.flags
            );
        }
        return native_make_closure(code, env);
    }
    let Some(context) = mmtk_control_context_mut() else {
        return native_make_closure(code, env);
    };
    let value = context
        .context_mut()
        .heap_mut()
        .allocate_compact_closure_i64(code, env)
        .raw() as i64;
    remember_compact_control_entry_from_heap(value, YObjectKind::Closure);
    value
}

fn make_thunk(code: usize, env: &[i64]) -> i64 {
    let capture = compact_control_capture_state();
    if !capture.is_empty() && capture.has_non_local_flow() {
        return native_make_thunk(code, env);
    }
    let contexts_enabled = !capture.is_empty() && compact_thunk_contexts_enabled();
    let sidecars_enabled =
        !capture.is_empty() && !contexts_enabled && compact_thunk_sidecars_enabled();
    if !capture.is_empty() && !contexts_enabled && !sidecars_enabled {
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
    remember_compact_control_entry_from_heap(thunk, YObjectKind::Thunk);
    if !capture.is_empty() {
        if sidecars_enabled {
            let native_thunk = native_make_thunk(code, env) as usize;
            if mmtk_cps_control_trace_enabled() {
                eprintln!("[MMTK-CPS] make_sidecar: compact={thunk:#x} native={native_thunk:#x}");
            }
            remember_compact_thunk_sidecar(thunk, native_thunk);
        } else {
            let context = unsafe { yulang_cps_capture_thunk_context_i64() };
            if mmtk_cps_control_trace_enabled() {
                eprintln!("[MMTK-CPS] make_context: compact={thunk:#x} context={context:#x}");
            }
            remember_compact_thunk_context(thunk, context);
        }
    }
    thunk
}

fn make_compact_thunk_with_context(
    code: usize,
    env_ptr: *const i64,
    env_len: usize,
    thunk_context: usize,
) -> i64 {
    let env = unsafe { native_i64_slice(env_ptr, env_len as i64) };
    let Some(context) = mmtk_control_context_mut() else {
        return native_make_thunk(code, &env);
    };
    let thunk = context
        .context_mut()
        .heap_mut()
        .allocate_compact_thunk_i64(code, &env)
        .raw() as i64;
    remember_compact_control_entry_from_heap(thunk, YObjectKind::Thunk);
    remember_compact_thunk_context(thunk, thunk_context);
    thunk
}

fn make_resumption(code: usize, env: &[i64]) -> i64 {
    let Some(context) = mmtk_control_context_mut() else {
        return 0;
    };
    let value = context
        .context_mut()
        .heap_mut()
        .allocate_compact_resumption_i64(code, env)
        .raw() as i64;
    remember_compact_control_entry_from_heap(value, YObjectKind::Resumption);
    value
}

fn native_cps_non_local_flow_active() -> bool {
    unsafe { yulang_cps_abort_active_i64() != 0 || yulang_cps_scope_return_active_i64() != 0 }
}

fn compact_thunk_sidecars_enabled() -> bool {
    match COMPACT_THUNK_SIDECARS_ENABLED.load(Ordering::Relaxed) {
        2 => true,
        1 => false,
        _ => {
            let enabled = std::env::var_os("YULANG_MMTK_CPS_CONTROL_THUNK_SIDECARS")
                .is_some_and(|value| value == "unsafe");
            COMPACT_THUNK_SIDECARS_ENABLED.store(if enabled { 2 } else { 1 }, Ordering::Relaxed);
            enabled
        }
    }
}

fn compact_thunk_contexts_enabled() -> bool {
    match COMPACT_THUNK_CONTEXTS_ENABLED.load(Ordering::Relaxed) {
        2 => true,
        1 => false,
        _ => {
            let enabled = std::env::var_os("YULANG_MMTK_CPS_CONTROL_THUNK_CONTEXTS")
                .is_some_and(|value| value == "unsafe");
            COMPACT_THUNK_CONTEXTS_ENABLED.store(if enabled { 2 } else { 1 }, Ordering::Relaxed);
            enabled
        }
    }
}

fn mmtk_cps_control_trace_enabled() -> bool {
    std::env::var_os("YULANG_MMTK_CPS_CONTROL_TRACE").is_some_and(|value| value == "1")
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct CompactControlCaptureState {
    flags: i64,
}

impl CompactControlCaptureState {
    fn is_empty(self) -> bool {
        self.flags == 0
    }

    fn has_closure_unsafe_state(self) -> bool {
        (self.flags & CONTROL_CAPTURE_CLOSURE_UNSAFE) != 0
    }

    fn has_non_local_flow(self) -> bool {
        (self.flags & CONTROL_CAPTURE_NON_LOCAL_FLOW) != 0
    }
}

fn compact_control_capture_state() -> CompactControlCaptureState {
    CompactControlCaptureState {
        flags: unsafe { yulang_cps_control_capture_context_flags_i64() },
    }
}

fn remember_compact_thunk_sidecar(value: i64, native_thunk: usize) {
    MMTK_CPS_CONTROL_THUNK_SIDECARS.with(|sidecars| {
        sidecars.borrow_mut().insert(value, native_thunk);
    });
}

fn compact_thunk_sidecar(value: i64) -> Option<usize> {
    MMTK_CPS_CONTROL_THUNK_SIDECARS.with(|sidecars| sidecars.borrow().get(&value).copied())
}

fn remember_compact_thunk_context(value: i64, context: usize) {
    MMTK_CPS_CONTROL_THUNK_CONTEXTS.with(|contexts| {
        contexts.borrow_mut().insert(value, context);
    });
}

fn compact_thunk_context(value: i64) -> Option<usize> {
    MMTK_CPS_CONTROL_THUNK_CONTEXTS.with(|contexts| contexts.borrow().get(&value).copied())
}

#[derive(Debug, Clone, Copy)]
struct CompactControlEntry {
    kind: YObjectKind,
    code: u64,
    env_ptr: *const i64,
    env_len: usize,
}

fn remember_compact_control_entry_from_heap(value: i64, kind: YObjectKind) {
    let raw = YValue::from_raw(value as usize);
    let Some(context) = mmtk_control_context_mut() else {
        return;
    };
    let Some((code, env_ptr)) = context
        .context()
        .heap()
        .compact_control_entry_parts(raw, kind)
    else {
        return;
    };
    let Some(env_len) = context.context().heap().compact_control_env_len(raw) else {
        return;
    };
    MMTK_CPS_CONTROL_ENTRIES.with(|entries| {
        entries.borrow_mut().insert(
            value,
            CompactControlEntry {
                kind,
                code,
                env_ptr,
                env_len,
            },
        );
    });
}

fn compact_control_entry(value: i64, kind: YObjectKind) -> Option<CompactControlEntry> {
    MMTK_CPS_CONTROL_ENTRIES.with(|entries| {
        let entry = entries.borrow().get(&value).copied()?;
        (entry.kind == kind).then_some(entry)
    })
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
    if let Some(entry) = compact_control_entry(value, kind) {
        return Some((entry.code, entry.env_ptr));
    }
    let value = YValue::from_raw(value as usize);
    mmtk_control_context_mut()?
        .context()
        .heap()
        .compact_control_entry_parts(value, kind)
}

fn compact_control_env_len(value: i64) -> Option<usize> {
    if let Some(entry) = compact_control_entry(value, YObjectKind::Thunk) {
        return Some(entry.env_len);
    }
    let value = YValue::from_raw(value as usize);
    mmtk_control_context_mut()?
        .context()
        .heap()
        .compact_control_env_len(value)
}

fn is_compact_control_kind(value: i64, kind: YObjectKind) -> bool {
    if compact_control_entry(value, kind).is_some() {
        return true;
    }
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

    extern "C" fn thunk_capture_flags(_env: *const i64) -> i64 {
        compact_control_capture_state().flags
    }

    unsafe extern "C" {
        fn yulang_cps_reset_i64();
        fn yulang_cps_install_handler_i64(handler: i64, consumes_mask: i64) -> i64;
        fn yulang_cps_uninstall_handler_i64(handler: i64) -> i64;
        fn yulang_cps_capture_handler_env_i64(handler: i64, entry: i64, env: i64) -> i64;
        fn yulang_cps_set_pending_escape_env_targets_i64(ptr: *const i64, len: i64) -> i64;
        fn yulang_cps_abort_i64(value: i64) -> i64;
        fn yulang_cps_clear_abort_i64() -> i64;
        fn yulang_cps_scope_return_i64(prompt: i64, target: i64, value: i64) -> i64;
        fn yulang_cps_clear_scope_return_i64() -> i64;
    }

    fn reset_control_test_state() {
        yulang_mmtk_cps_reset_i64();
        unsafe {
            yulang_cps_reset_i64();
        }
    }

    fn assert_capture_flags(expected: i64) {
        assert_eq!(compact_control_capture_state().flags, expected);
        assert_eq!(
            unsafe { yulang_cps_control_capture_context_is_empty_i64() },
            i64::from(expected == 0)
        );
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
    fn mmtk_cps_control_closure_stays_compact_under_direct_handler_and_guard_state() {
        let _guard = mmtk_test_lock();
        reset_control_test_state();

        unsafe {
            yulang_cps_fresh_guard_i64();
        }
        let guarded = yulang_mmtk_cps_control_make_closure_i64_1(add_env as *const () as usize, 40);
        assert!(is_compact_control_kind(guarded, YObjectKind::Closure));
        assert_eq!(yulang_mmtk_cps_control_apply_closure_i64(guarded, 2), 42);

        reset_control_test_state();
        unsafe {
            yulang_cps_install_handler_i64(7, -1);
        }
        let handled = yulang_mmtk_cps_control_make_closure_i64_1(add_env as *const () as usize, 40);
        assert!(is_compact_control_kind(handled, YObjectKind::Closure));
        assert_eq!(yulang_mmtk_cps_control_apply_closure_i64(handled, 2), 42);
        unsafe {
            yulang_cps_uninstall_handler_i64(7);
        }
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
    fn mmtk_cps_control_capture_flags_cover_direct_native_state() {
        let _guard = mmtk_test_lock();
        reset_control_test_state();
        assert_capture_flags(0);

        unsafe {
            yulang_cps_fresh_guard_i64();
        }
        assert_capture_flags(CONTROL_CAPTURE_GUARD_STACK);

        reset_control_test_state();
        unsafe {
            yulang_cps_install_handler_i64(7, -1);
        }
        assert_capture_flags(CONTROL_CAPTURE_HANDLER_STACK);
        unsafe {
            yulang_cps_uninstall_handler_i64(7);
        }
        assert_capture_flags(0);
    }

    #[test]
    fn mmtk_cps_control_capture_flags_cover_pending_native_state() {
        let _guard = mmtk_test_lock();
        reset_control_test_state();

        unsafe {
            yulang_cps_capture_handler_env_i64(7, 11, 13);
        }
        assert_capture_flags(CONTROL_CAPTURE_PENDING_HANDLER_ENVS);

        reset_control_test_state();
        let targets = [3, 5, 8];
        unsafe {
            yulang_cps_set_pending_escape_env_targets_i64(targets.as_ptr(), targets.len() as i64);
        }
        assert_capture_flags(CONTROL_CAPTURE_PENDING_ESCAPE_TARGETS);
    }

    #[test]
    fn mmtk_cps_control_capture_flags_cover_active_blocked_thunk_state() {
        let _guard = mmtk_test_lock();
        reset_control_test_state();

        let thunk =
            unsafe { yulang_cps_make_thunk_i64_0(thunk_capture_flags as *const () as usize) };
        let bounded = unsafe { yulang_cps_add_thunk_boundary_i64(thunk, 7, 0, 1) };
        let flags = unsafe { yulang_cps_force_thunk_i64(bounded) };
        assert_eq!(
            flags & CONTROL_CAPTURE_ACTIVE_BLOCKED,
            CONTROL_CAPTURE_ACTIVE_BLOCKED
        );
        assert_capture_flags(0);
    }

    #[test]
    fn mmtk_cps_control_capture_flags_cover_non_local_flow_state() {
        let _guard = mmtk_test_lock();
        reset_control_test_state();

        unsafe {
            yulang_cps_abort_i64(123);
        }
        assert_capture_flags(CONTROL_CAPTURE_ABORT);
        unsafe {
            yulang_cps_clear_abort_i64();
        }
        assert_capture_flags(0);

        unsafe {
            yulang_cps_scope_return_i64(1, 2, 3);
        }
        assert_capture_flags(CONTROL_CAPTURE_SCOPE_RETURN);
        unsafe {
            yulang_cps_clear_scope_return_i64();
        }
        assert_capture_flags(0);
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
    fn mmtk_cps_control_thunk_context_preserves_non_empty_capture_context() {
        let _guard = mmtk_test_lock();
        unsafe {
            std::env::set_var("YULANG_MMTK_CPS_CONTROL_THUNK_CONTEXTS", "unsafe");
        }
        reset_control_test_state();

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
        assert!(compact_thunk_context(thunk).is_some());
        assert!(compact_thunk_sidecar(thunk).is_none());
        assert_eq!(yulang_mmtk_cps_control_force_thunk_i64(thunk), 99);

        let bounded = yulang_mmtk_cps_control_add_thunk_boundary_i64(thunk, 1, i64::MAX, 1);
        assert!(is_compact_control_kind(bounded, YObjectKind::Thunk));
        assert!(compact_thunk_context(bounded).is_some());
        assert_eq!(yulang_mmtk_cps_control_force_thunk_i64(bounded), 99);

        unsafe {
            std::env::remove_var("YULANG_MMTK_CPS_CONTROL_THUNK_CONTEXTS");
        }
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

    #[test]
    fn mmtk_cps_control_thunk_sidecar_does_not_cross_non_local_flow() {
        let _guard = mmtk_test_lock();
        unsafe {
            std::env::set_var("YULANG_MMTK_CPS_CONTROL_THUNK_SIDECARS", "unsafe");
        }
        reset_control_test_state();

        unsafe {
            yulang_cps_abort_i64(123);
        }
        assert!(compact_control_capture_state().has_non_local_flow());
        let thunk = yulang_mmtk_cps_control_make_thunk_i64_1(thunk_value as *const () as usize, 99);
        assert_eq!(yulang_mmtk_cps_control_is_thunk_i64(thunk), 1);
        assert!(!is_compact_control_kind(thunk, YObjectKind::Thunk));
        assert!(compact_thunk_sidecar(thunk).is_none());

        unsafe {
            yulang_cps_clear_abort_i64();
            std::env::remove_var("YULANG_MMTK_CPS_CONTROL_THUNK_SIDECARS");
        }
    }
}
