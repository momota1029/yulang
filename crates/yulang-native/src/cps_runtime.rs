//! Runtime support symbols used by CPS-repr native executables.
//!
//! The generated CPS object still calls a tiny C ABI for heap-allocated
//! resumptions and captured continuation environments.  Keeping those helpers
//! here makes the ABI type-checked Rust code instead of generated harness text.

use std::cell::RefCell;
use std::collections::{HashMap, HashSet};
use std::io::Write;
use std::ptr;

type YulangCpsI64Continuation = unsafe extern "C" fn(*const i64, i64) -> i64;
type YulangCpsI64ThunkEntry = unsafe extern "C" fn(*const i64) -> i64;
type YulangCpsI64ClosureEntry = unsafe extern "C" fn(*const i64, i64) -> i64;

#[repr(C)]
struct YulangCpsI64Resumption {
    code: YulangCpsI64Continuation,
    env: *const i64,
    handlers: Box<[YulangCpsI64HandlerFrame]>,
    guard_stack: Box<[i64]>,
}

#[repr(C)]
struct YulangCpsI64Thunk {
    code: YulangCpsI64ThunkEntry,
    env: *const i64,
    handlers: Box<[YulangCpsI64HandlerFrame]>,
    guard_stack: Box<[i64]>,
}

#[repr(C)]
struct YulangCpsI64Closure {
    code: YulangCpsI64ClosureEntry,
    env: *const i64,
    handlers: Box<[YulangCpsI64HandlerFrame]>,
    guard_stack: Box<[i64]>,
}

enum YulangCpsI64HeapValue {
    Tuple(Box<[i64]>),
    Variant { tag: i64, value: Option<i64> },
    List(Vec<i64>),
}

#[derive(Clone)]
struct YulangCpsI64HandlerFrame {
    handler: i64,
    guard_stack: Box<[i64]>,
    envs: Vec<YulangCpsI64HandlerEnv>,
}

#[derive(Clone)]
struct YulangCpsI64HandlerEnv {
    entry: i64,
    env: i64,
}

thread_local! {
    static YULANG_CPS_I64_HEAP_VALUES: RefCell<HashSet<i64>> = RefCell::new(HashSet::new());
    static YULANG_CPS_I64_TAG_NAMES: RefCell<HashMap<i64, Box<str>>> = RefCell::new(HashMap::new());
    static YULANG_CPS_I64_THUNKS: RefCell<HashSet<isize>> = RefCell::new(HashSet::new());
    static YULANG_CPS_I64_HANDLER_STACK: RefCell<Vec<YulangCpsI64HandlerFrame>> = const { RefCell::new(Vec::new()) };
    static YULANG_CPS_I64_GUARD_STACK: RefCell<Vec<i64>> = const { RefCell::new(Vec::new()) };
    static YULANG_CPS_I64_NEXT_GUARD: RefCell<i64> = const { RefCell::new(0) };
    static YULANG_CPS_I64_PENDING_HANDLER_ENVS: RefCell<Vec<(i64, YulangCpsI64HandlerEnv)>> = const { RefCell::new(Vec::new()) };
    static YULANG_CPS_I64_SELECTED_HANDLER_ENVS: RefCell<Vec<YulangCpsI64HandlerEnv>> = const { RefCell::new(Vec::new()) };
}

fn make_env(values: &[i64]) -> *const i64 {
    if values.is_empty() {
        return ptr::null();
    }
    Box::leak(values.to_vec().into_boxed_slice()).as_ptr()
}

fn heap_value(value: YulangCpsI64HeapValue) -> i64 {
    let pointer = Box::into_raw(Box::new(value)) as i64;
    YULANG_CPS_I64_HEAP_VALUES.with(|values| {
        values.borrow_mut().insert(pointer);
    });
    pointer
}

fn tag_hash(tag: &str) -> i64 {
    let mut hash = 0xcbf29ce484222325_u64;
    for byte in tag.as_bytes() {
        hash ^= u64::from(*byte);
        hash = hash.wrapping_mul(0x100000001b3);
    }
    hash as i64
}

fn variant_value(tag: &str, value: Option<i64>) -> i64 {
    let hash = tag_hash(tag);
    register_tag_name(hash, tag);
    heap_value(YulangCpsI64HeapValue::Variant { tag: hash, value })
}

fn register_tag_name(tag: i64, name: &str) {
    YULANG_CPS_I64_TAG_NAMES.with(|names| {
        names
            .borrow_mut()
            .entry(tag)
            .or_insert_with(|| name.to_string().into_boxed_str());
    });
}

fn tag_name(tag: i64) -> String {
    YULANG_CPS_I64_TAG_NAMES.with(|names| {
        names
            .borrow()
            .get(&tag)
            .map(|name| name.to_string())
            .unwrap_or_else(|| format!("#{tag:x}"))
    })
}

fn is_heap_value(value: i64) -> bool {
    YULANG_CPS_I64_HEAP_VALUES.with(|values| values.borrow().contains(&value))
}

fn print_i64_value(value: i64) {
    if !is_heap_value(value) {
        print!("{value}");
        return;
    }
    let value = unsafe { &*(value as *const YulangCpsI64HeapValue) };
    match value {
        YulangCpsI64HeapValue::Tuple(items) => {
            print!("(");
            for (index, item) in items.iter().enumerate() {
                if index > 0 {
                    print!(", ");
                }
                print_i64_value(*item);
            }
            print!(")");
        }
        YulangCpsI64HeapValue::Variant { tag, value } => {
            print!(":{}", tag_name(*tag));
            if let Some(value) = value {
                print!(" ");
                print_i64_value(*value);
            }
        }
        YulangCpsI64HeapValue::List(items) => {
            print!("[");
            for (index, item) in items.iter().enumerate() {
                if index > 0 {
                    print!(", ");
                }
                print_i64_value(*item);
            }
            print!("]");
        }
    }
}

fn current_guard_stack() -> Vec<i64> {
    YULANG_CPS_I64_GUARD_STACK.with(|stack| stack.borrow().clone())
}

fn current_handler_stack_with_fallback(fallback: i64) -> Vec<YulangCpsI64HandlerFrame> {
    YULANG_CPS_I64_HANDLER_STACK.with(|stack| {
        let stack = stack.borrow();
        if stack.is_empty() && fallback >= 0 {
            vec![YulangCpsI64HandlerFrame {
                handler: fallback,
                guard_stack: current_guard_stack().into_boxed_slice(),
                envs: Vec::new(),
            }]
        } else {
            stack.clone()
        }
    })
}

fn take_pending_handler_frames() -> Vec<YulangCpsI64HandlerFrame> {
    let pending =
        YULANG_CPS_I64_PENDING_HANDLER_ENVS.with(|envs| std::mem::take(&mut *envs.borrow_mut()));
    let mut frames: Vec<YulangCpsI64HandlerFrame> = Vec::new();
    for (handler, env) in pending {
        if let Some(frame) = frames.iter_mut().find(|frame| frame.handler == handler) {
            frame.envs.push(env);
        } else {
            frames.push(YulangCpsI64HandlerFrame {
                handler,
                guard_stack: current_guard_stack().into_boxed_slice(),
                envs: vec![env],
            });
        }
    }
    frames
}

fn take_pending_handler_envs(handler: i64) -> Vec<YulangCpsI64HandlerEnv> {
    YULANG_CPS_I64_PENDING_HANDLER_ENVS.with(|envs| {
        let mut envs = envs.borrow_mut();
        let mut selected = Vec::new();
        let mut index = 0;
        while index < envs.len() {
            if envs[index].0 == handler {
                selected.push(envs.remove(index).1);
            } else {
                index += 1;
            }
        }
        selected
    })
}

fn with_cps_state<T>(
    handlers: Vec<YulangCpsI64HandlerFrame>,
    guard_stack: Vec<i64>,
    run: impl FnOnce() -> T,
) -> T {
    let previous_handlers = YULANG_CPS_I64_HANDLER_STACK
        .with(|stack| std::mem::replace(&mut *stack.borrow_mut(), handlers));
    let previous_guards = YULANG_CPS_I64_GUARD_STACK
        .with(|stack| std::mem::replace(&mut *stack.borrow_mut(), guard_stack));
    let result = run();
    YULANG_CPS_I64_HANDLER_STACK.with(|stack| *stack.borrow_mut() = previous_handlers);
    YULANG_CPS_I64_GUARD_STACK.with(|stack| *stack.borrow_mut() = previous_guards);
    result
}

fn handler_stack_with_captured(
    captured: &[YulangCpsI64HandlerFrame],
) -> Vec<YulangCpsI64HandlerFrame> {
    let mut handlers = YULANG_CPS_I64_HANDLER_STACK.with(|stack| stack.borrow().clone());
    handlers.extend(captured.iter().cloned());
    handlers
}

fn handler_stack_for_force(captured: &[YulangCpsI64HandlerFrame]) -> Vec<YulangCpsI64HandlerFrame> {
    let mut handlers = handler_stack_with_captured(captured);
    handlers.extend(take_pending_handler_frames());
    handlers
}

fn make_resumption(code: isize, fallback_handler: i64, values: &[i64]) -> isize {
    let code = unsafe { std::mem::transmute::<usize, YulangCpsI64Continuation>(code as usize) };
    Box::into_raw(Box::new(YulangCpsI64Resumption {
        code,
        env: make_env(values),
        handlers: current_handler_stack_with_fallback(fallback_handler).into_boxed_slice(),
        guard_stack: current_guard_stack().into_boxed_slice(),
    })) as isize
}

fn make_thunk(code: isize, values: &[i64]) -> isize {
    let code = unsafe { std::mem::transmute::<usize, YulangCpsI64ThunkEntry>(code as usize) };
    let mut handlers = YULANG_CPS_I64_HANDLER_STACK.with(|stack| stack.borrow().clone());
    handlers.extend(take_pending_handler_frames());
    let ptr = Box::into_raw(Box::new(YulangCpsI64Thunk {
        code,
        env: make_env(values),
        handlers: handlers.into_boxed_slice(),
        guard_stack: current_guard_stack().into_boxed_slice(),
    })) as isize;
    YULANG_CPS_I64_THUNKS.with(|thunks| {
        thunks.borrow_mut().insert(ptr);
    });
    ptr
}

fn make_closure(code: isize, values: &[i64]) -> isize {
    let code = unsafe { std::mem::transmute::<usize, YulangCpsI64ClosureEntry>(code as usize) };
    let mut handlers = YULANG_CPS_I64_HANDLER_STACK.with(|stack| stack.borrow().clone());
    handlers.extend(take_pending_handler_frames());
    Box::into_raw(Box::new(YulangCpsI64Closure {
        code,
        env: make_env(values),
        handlers: handlers.into_boxed_slice(),
        guard_stack: current_guard_stack().into_boxed_slice(),
    })) as isize
}

fn make_recursive_closure(code: isize, self_slot: usize, values: &[i64]) -> isize {
    let code = unsafe { std::mem::transmute::<usize, YulangCpsI64ClosureEntry>(code as usize) };
    let closure = Box::into_raw(Box::new(YulangCpsI64Closure {
        code,
        env: ptr::null(),
        handlers: Box::new([]),
        guard_stack: Box::new([]),
    }));
    let ptr = closure as isize;
    let mut values = values.to_vec();
    if self_slot < values.len() {
        values[self_slot] = ptr as i64;
    }
    unsafe {
        (*closure).env = make_env(&values);
        let mut handlers = YULANG_CPS_I64_HANDLER_STACK.with(|stack| stack.borrow().clone());
        handlers.extend(take_pending_handler_frames());
        (*closure).handlers = handlers.into_boxed_slice();
        (*closure).guard_stack = current_guard_stack().into_boxed_slice();
    }
    ptr
}

#[unsafe(no_mangle)]
pub extern "C" fn yulang_cps_make_resumption_i64_0(code: isize, handler: i64) -> isize {
    make_resumption(code, handler, &[])
}

#[unsafe(no_mangle)]
pub extern "C" fn yulang_cps_make_resumption_i64_1(code: isize, handler: i64, a: i64) -> isize {
    make_resumption(code, handler, &[a])
}

#[unsafe(no_mangle)]
pub extern "C" fn yulang_cps_make_resumption_i64_2(
    code: isize,
    handler: i64,
    a: i64,
    b: i64,
) -> isize {
    make_resumption(code, handler, &[a, b])
}

#[unsafe(no_mangle)]
pub extern "C" fn yulang_cps_make_resumption_i64_3(
    code: isize,
    handler: i64,
    a: i64,
    b: i64,
    c: i64,
) -> isize {
    make_resumption(code, handler, &[a, b, c])
}

#[unsafe(no_mangle)]
pub extern "C" fn yulang_cps_make_resumption_i64_4(
    code: isize,
    handler: i64,
    a: i64,
    b: i64,
    c: i64,
    d: i64,
) -> isize {
    make_resumption(code, handler, &[a, b, c, d])
}

#[unsafe(no_mangle)]
pub extern "C" fn yulang_cps_make_env_i64_0() -> isize {
    make_env(&[]) as isize
}

#[unsafe(no_mangle)]
pub extern "C" fn yulang_cps_make_env_i64_1(a: i64) -> isize {
    make_env(&[a]) as isize
}

#[unsafe(no_mangle)]
pub extern "C" fn yulang_cps_make_env_i64_2(a: i64, b: i64) -> isize {
    make_env(&[a, b]) as isize
}

#[unsafe(no_mangle)]
pub extern "C" fn yulang_cps_make_env_i64_3(a: i64, b: i64, c: i64) -> isize {
    make_env(&[a, b, c]) as isize
}

#[unsafe(no_mangle)]
pub extern "C" fn yulang_cps_make_env_i64_4(a: i64, b: i64, c: i64, d: i64) -> isize {
    make_env(&[a, b, c, d]) as isize
}

#[unsafe(no_mangle)]
pub extern "C" fn yulang_cps_resume_i64(value: isize, arg: i64) -> i64 {
    let resumption = unsafe { &*(value as *const YulangCpsI64Resumption) };
    with_cps_state(
        resumption.handlers.to_vec(),
        resumption.guard_stack.to_vec(),
        || unsafe { (resumption.code)(resumption.env, arg) },
    )
}

#[unsafe(no_mangle)]
pub extern "C" fn yulang_cps_resume_with_handler_i64(value: isize, arg: i64, handler: i64) -> i64 {
    let resumption = unsafe { &*(value as *const YulangCpsI64Resumption) };
    let mut handlers = resumption.handlers.to_vec();
    handlers.push(YulangCpsI64HandlerFrame {
        handler,
        guard_stack: current_guard_stack().into_boxed_slice(),
        envs: take_pending_handler_envs(handler),
    });
    with_cps_state(handlers, resumption.guard_stack.to_vec(), || unsafe {
        (resumption.code)(resumption.env, arg)
    })
}

#[unsafe(no_mangle)]
pub extern "C" fn yulang_cps_select_handler_i64(
    fallback_handler: i64,
    allowed_mask: i64,
    blocked: i64,
) -> i64 {
    let stack = current_handler_stack_with_fallback(fallback_handler);
    for (index, frame) in stack.iter().enumerate().rev() {
        let allowed = (allowed_mask & (1_i64 << frame.handler)) != 0;
        if !allowed {
            continue;
        }
        if blocked >= 0 && frame.guard_stack.contains(&blocked) {
            continue;
        }
        YULANG_CPS_I64_HANDLER_STACK.with(|active| {
            *active.borrow_mut() = stack[..index].to_vec();
        });
        YULANG_CPS_I64_SELECTED_HANDLER_ENVS.with(|envs| {
            *envs.borrow_mut() = frame.envs.to_vec();
        });
        return frame.handler;
    }
    YULANG_CPS_I64_SELECTED_HANDLER_ENVS.with(|envs| envs.borrow_mut().clear());
    -1
}

#[unsafe(no_mangle)]
pub extern "C" fn yulang_cps_capture_handler_env_i64(handler: i64, entry: i64, env: i64) -> i64 {
    YULANG_CPS_I64_PENDING_HANDLER_ENVS.with(|envs| {
        envs.borrow_mut()
            .push((handler, YulangCpsI64HandlerEnv { entry, env }));
    });
    0
}

#[unsafe(no_mangle)]
pub extern "C" fn yulang_cps_selected_handler_env_or_i64(entry: i64, fallback: i64) -> i64 {
    YULANG_CPS_I64_SELECTED_HANDLER_ENVS.with(|envs| {
        envs.borrow()
            .iter()
            .find(|env| env.entry == entry)
            .map(|env| env.env)
            .unwrap_or(fallback)
    })
}

#[unsafe(no_mangle)]
pub extern "C" fn yulang_cps_make_thunk_i64_0(code: isize) -> isize {
    make_thunk(code, &[])
}

#[unsafe(no_mangle)]
pub extern "C" fn yulang_cps_make_thunk_i64_1(code: isize, a: i64) -> isize {
    make_thunk(code, &[a])
}

#[unsafe(no_mangle)]
pub extern "C" fn yulang_cps_make_thunk_i64_2(code: isize, a: i64, b: i64) -> isize {
    make_thunk(code, &[a, b])
}

#[unsafe(no_mangle)]
pub extern "C" fn yulang_cps_make_thunk_i64_3(code: isize, a: i64, b: i64, c: i64) -> isize {
    make_thunk(code, &[a, b, c])
}

#[unsafe(no_mangle)]
pub extern "C" fn yulang_cps_make_thunk_i64_4(
    code: isize,
    a: i64,
    b: i64,
    c: i64,
    d: i64,
) -> isize {
    make_thunk(code, &[a, b, c, d])
}

#[unsafe(no_mangle)]
pub extern "C" fn yulang_cps_make_closure_i64_0(code: isize) -> isize {
    make_closure(code, &[])
}

#[unsafe(no_mangle)]
pub extern "C" fn yulang_cps_make_closure_i64_1(code: isize, a: i64) -> isize {
    make_closure(code, &[a])
}

#[unsafe(no_mangle)]
pub extern "C" fn yulang_cps_make_closure_i64_2(code: isize, a: i64, b: i64) -> isize {
    make_closure(code, &[a, b])
}

#[unsafe(no_mangle)]
pub extern "C" fn yulang_cps_make_closure_i64_3(code: isize, a: i64, b: i64, c: i64) -> isize {
    make_closure(code, &[a, b, c])
}

#[unsafe(no_mangle)]
pub extern "C" fn yulang_cps_make_closure_i64_4(
    code: isize,
    a: i64,
    b: i64,
    c: i64,
    d: i64,
) -> isize {
    make_closure(code, &[a, b, c, d])
}

#[unsafe(no_mangle)]
pub extern "C" fn yulang_cps_make_recursive_closure_i64_0(code: isize, self_slot: i64) -> isize {
    make_recursive_closure(code, self_slot as usize, &[])
}

#[unsafe(no_mangle)]
pub extern "C" fn yulang_cps_make_recursive_closure_i64_1(
    code: isize,
    self_slot: i64,
    a: i64,
) -> isize {
    make_recursive_closure(code, self_slot as usize, &[a])
}

#[unsafe(no_mangle)]
pub extern "C" fn yulang_cps_make_recursive_closure_i64_2(
    code: isize,
    self_slot: i64,
    a: i64,
    b: i64,
) -> isize {
    make_recursive_closure(code, self_slot as usize, &[a, b])
}

#[unsafe(no_mangle)]
pub extern "C" fn yulang_cps_make_recursive_closure_i64_3(
    code: isize,
    self_slot: i64,
    a: i64,
    b: i64,
    c: i64,
) -> isize {
    make_recursive_closure(code, self_slot as usize, &[a, b, c])
}

#[unsafe(no_mangle)]
pub extern "C" fn yulang_cps_make_recursive_closure_i64_4(
    code: isize,
    self_slot: i64,
    a: i64,
    b: i64,
    c: i64,
    d: i64,
) -> isize {
    make_recursive_closure(code, self_slot as usize, &[a, b, c, d])
}

#[unsafe(no_mangle)]
pub extern "C" fn yulang_cps_apply_closure_i64(value: isize, arg: i64) -> i64 {
    let closure = unsafe { &*(value as *const YulangCpsI64Closure) };
    with_cps_state(
        handler_stack_with_captured(&closure.handlers),
        closure.guard_stack.to_vec(),
        || unsafe { (closure.code)(closure.env, arg) },
    )
}

#[unsafe(no_mangle)]
pub extern "C" fn yulang_cps_tuple_i64_0() -> i64 {
    heap_value(YulangCpsI64HeapValue::Tuple(Vec::new().into_boxed_slice()))
}

#[unsafe(no_mangle)]
pub extern "C" fn yulang_cps_tuple_i64_1(a: i64) -> i64 {
    heap_value(YulangCpsI64HeapValue::Tuple(vec![a].into_boxed_slice()))
}

#[unsafe(no_mangle)]
pub extern "C" fn yulang_cps_tuple_i64_2(a: i64, b: i64) -> i64 {
    heap_value(YulangCpsI64HeapValue::Tuple(vec![a, b].into_boxed_slice()))
}

#[unsafe(no_mangle)]
pub extern "C" fn yulang_cps_tuple_i64_3(a: i64, b: i64, c: i64) -> i64 {
    heap_value(YulangCpsI64HeapValue::Tuple(
        vec![a, b, c].into_boxed_slice(),
    ))
}

#[unsafe(no_mangle)]
pub extern "C" fn yulang_cps_tuple_i64_4(a: i64, b: i64, c: i64, d: i64) -> i64 {
    heap_value(YulangCpsI64HeapValue::Tuple(
        vec![a, b, c, d].into_boxed_slice(),
    ))
}

#[unsafe(no_mangle)]
pub extern "C" fn yulang_cps_tuple_get_i64(value: i64, index: i64) -> i64 {
    let value = unsafe { &*(value as *const YulangCpsI64HeapValue) };
    let YulangCpsI64HeapValue::Tuple(items) = value else {
        return 0;
    };
    items.get(index as usize).copied().unwrap_or(0)
}

#[unsafe(no_mangle)]
pub extern "C" fn yulang_cps_register_tag_i64(tag: i64, ptr: *const u8, len: i64) -> i64 {
    if ptr.is_null() || len < 0 {
        return 0;
    }
    let Ok(len) = usize::try_from(len) else {
        return 0;
    };
    let bytes = unsafe { std::slice::from_raw_parts(ptr, len) };
    let Ok(name) = std::str::from_utf8(bytes) else {
        return 0;
    };
    register_tag_name(tag, name);
    0
}

#[unsafe(no_mangle)]
pub extern "C" fn yulang_cps_print_i64(value: i64) {
    print_i64_value(value);
    let _ = std::io::stdout().flush();
}

#[unsafe(no_mangle)]
pub extern "C" fn yulang_cps_variant_i64_0(tag: i64) -> i64 {
    heap_value(YulangCpsI64HeapValue::Variant { tag, value: None })
}

#[unsafe(no_mangle)]
pub extern "C" fn yulang_cps_variant_i64_1(tag: i64, value: i64) -> i64 {
    heap_value(YulangCpsI64HeapValue::Variant {
        tag,
        value: Some(value),
    })
}

#[unsafe(no_mangle)]
pub extern "C" fn yulang_cps_variant_tag_eq_i64(value: i64, tag: i64) -> i64 {
    let value = unsafe { &*(value as *const YulangCpsI64HeapValue) };
    match value {
        YulangCpsI64HeapValue::Variant { tag: actual, .. } => i64::from(*actual == tag),
        _ => 0,
    }
}

#[unsafe(no_mangle)]
pub extern "C" fn yulang_cps_variant_payload_i64(value: i64) -> i64 {
    let value = unsafe { &*(value as *const YulangCpsI64HeapValue) };
    match value {
        YulangCpsI64HeapValue::Variant {
            value: Some(value), ..
        } => *value,
        _ => 0,
    }
}

#[unsafe(no_mangle)]
pub extern "C" fn yulang_cps_list_empty_i64() -> i64 {
    heap_value(YulangCpsI64HeapValue::List(Vec::new()))
}

#[unsafe(no_mangle)]
pub extern "C" fn yulang_cps_list_singleton_i64(value: i64) -> i64 {
    heap_value(YulangCpsI64HeapValue::List(vec![value]))
}

#[unsafe(no_mangle)]
pub extern "C" fn yulang_cps_list_merge_i64(left: i64, right: i64) -> i64 {
    let left = unsafe { &*(left as *const YulangCpsI64HeapValue) };
    let right = unsafe { &*(right as *const YulangCpsI64HeapValue) };
    let (YulangCpsI64HeapValue::List(left), YulangCpsI64HeapValue::List(right)) = (left, right)
    else {
        return yulang_cps_list_empty_i64();
    };
    let mut merged = left.clone();
    merged.extend(right.iter().copied());
    heap_value(YulangCpsI64HeapValue::List(merged))
}

#[unsafe(no_mangle)]
pub extern "C" fn yulang_cps_list_len_i64(value: i64) -> i64 {
    let value = unsafe { &*(value as *const YulangCpsI64HeapValue) };
    match value {
        YulangCpsI64HeapValue::List(items) => items.len() as i64,
        _ => 0,
    }
}

#[unsafe(no_mangle)]
pub extern "C" fn yulang_cps_list_index_i64(value: i64, index: i64) -> i64 {
    let value = unsafe { &*(value as *const YulangCpsI64HeapValue) };
    let YulangCpsI64HeapValue::List(items) = value else {
        return 0;
    };
    items.get(index as usize).copied().unwrap_or(0)
}

#[unsafe(no_mangle)]
pub extern "C" fn yulang_cps_list_index_range_raw_i64(value: i64, start: i64, end: i64) -> i64 {
    let value = unsafe { &*(value as *const YulangCpsI64HeapValue) };
    let YulangCpsI64HeapValue::List(items) = value else {
        return yulang_cps_list_empty_i64();
    };
    let Ok(start) = usize::try_from(start) else {
        return yulang_cps_list_empty_i64();
    };
    let Ok(end) = usize::try_from(end) else {
        return yulang_cps_list_empty_i64();
    };
    if start > end || end > items.len() {
        return yulang_cps_list_empty_i64();
    }
    heap_value(YulangCpsI64HeapValue::List(items[start..end].to_vec()))
}

#[unsafe(no_mangle)]
pub extern "C" fn yulang_cps_list_splice_raw_i64(
    value: i64,
    start: i64,
    end: i64,
    insert: i64,
) -> i64 {
    let value = unsafe { &*(value as *const YulangCpsI64HeapValue) };
    let insert = unsafe { &*(insert as *const YulangCpsI64HeapValue) };
    let (YulangCpsI64HeapValue::List(items), YulangCpsI64HeapValue::List(insert)) = (value, insert)
    else {
        return yulang_cps_list_empty_i64();
    };
    let Ok(start) = usize::try_from(start) else {
        return yulang_cps_list_empty_i64();
    };
    let Ok(end) = usize::try_from(end) else {
        return yulang_cps_list_empty_i64();
    };
    if start > end || end > items.len() {
        return yulang_cps_list_empty_i64();
    }
    let mut result = Vec::with_capacity(items.len() - (end - start) + insert.len());
    result.extend_from_slice(&items[..start]);
    result.extend(insert.iter().copied());
    result.extend_from_slice(&items[end..]);
    heap_value(YulangCpsI64HeapValue::List(result))
}

#[unsafe(no_mangle)]
pub extern "C" fn yulang_cps_list_view_raw_i64(value: i64) -> i64 {
    let value = unsafe { &*(value as *const YulangCpsI64HeapValue) };
    let YulangCpsI64HeapValue::List(items) = value else {
        return variant_value("empty", None);
    };
    match items.len() {
        0 => variant_value("empty", None),
        1 => variant_value("leaf", items.first().copied()),
        len => {
            let mid = len / 2;
            let left = heap_value(YulangCpsI64HeapValue::List(items[..mid].to_vec()));
            let right = heap_value(YulangCpsI64HeapValue::List(items[mid..].to_vec()));
            let tuple = heap_value(YulangCpsI64HeapValue::Tuple(
                vec![left, right].into_boxed_slice(),
            ));
            variant_value("node", Some(tuple))
        }
    }
}

#[unsafe(no_mangle)]
pub extern "C" fn yulang_cps_force_thunk_i64(value: isize) -> i64 {
    let mut value = value;
    loop {
        let is_thunk = YULANG_CPS_I64_THUNKS.with(|thunks| thunks.borrow().contains(&value));
        if !is_thunk {
            return value as i64;
        }
        let thunk = unsafe { &*(value as *const YulangCpsI64Thunk) };
        value = with_cps_state(
            handler_stack_for_force(&thunk.handlers),
            thunk.guard_stack.to_vec(),
            || unsafe { (thunk.code)(thunk.env) },
        ) as isize;
    }
}

#[unsafe(no_mangle)]
pub extern "C" fn yulang_cps_fresh_guard_i64() -> i64 {
    let id = YULANG_CPS_I64_NEXT_GUARD.with(|next| {
        let mut next = next.borrow_mut();
        let id = *next;
        *next += 1;
        id
    });
    YULANG_CPS_I64_GUARD_STACK.with(|stack| {
        stack.borrow_mut().push(id);
    });
    id
}

#[unsafe(no_mangle)]
pub extern "C" fn yulang_cps_peek_guard_i64() -> i64 {
    YULANG_CPS_I64_GUARD_STACK.with(|stack| stack.borrow().last().copied().unwrap_or(0))
}

#[unsafe(no_mangle)]
pub extern "C" fn yulang_cps_find_guard_i64(id: i64) -> i64 {
    YULANG_CPS_I64_GUARD_STACK.with(|stack| i64::from(stack.borrow().contains(&id)))
}
