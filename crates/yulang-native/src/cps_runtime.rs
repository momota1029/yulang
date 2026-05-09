//! Runtime support symbols used by CPS-repr native executables.
//!
//! The generated CPS object still calls a tiny C ABI for heap-allocated
//! resumptions and captured continuation environments.  Keeping those helpers
//! here makes the ABI type-checked Rust code instead of generated harness text.

use std::cell::RefCell;
use std::collections::HashSet;
use std::ptr;

type YulangCpsI64Continuation = unsafe extern "C" fn(*const i64, i64) -> i64;
type YulangCpsI64ThunkEntry = unsafe extern "C" fn(*const i64) -> i64;

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

fn current_guard_stack() -> Vec<i64> {
    YULANG_CPS_I64_GUARD_STACK.with(|stack| stack.borrow().clone())
}

fn current_handler_stack_with_fallback(fallback: i64) -> Vec<YulangCpsI64HandlerFrame> {
    YULANG_CPS_I64_HANDLER_STACK.with(|stack| {
        let stack = stack.borrow();
        if stack.is_empty() {
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
pub extern "C" fn yulang_cps_force_thunk_i64(value: isize) -> i64 {
    let mut value = value;
    loop {
        let is_thunk = YULANG_CPS_I64_THUNKS.with(|thunks| thunks.borrow().contains(&value));
        if !is_thunk {
            return value as i64;
        }
        let thunk = unsafe { &*(value as *const YulangCpsI64Thunk) };
        value = with_cps_state(
            thunk.handlers.to_vec(),
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
