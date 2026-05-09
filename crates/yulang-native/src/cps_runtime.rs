//! Runtime support symbols used by CPS-repr native executables.
//!
//! The generated CPS object still calls a tiny C ABI for heap-allocated
//! resumptions and captured continuation environments.  Keeping those helpers
//! here makes the ABI type-checked Rust code instead of generated harness text.

use std::ptr;

type YulangCpsI64Continuation = unsafe extern "C" fn(*const i64, i64) -> i64;

#[repr(C)]
struct YulangCpsI64Resumption {
    code: YulangCpsI64Continuation,
    env: *const i64,
}

fn make_env(values: &[i64]) -> *const i64 {
    if values.is_empty() {
        return ptr::null();
    }
    Box::leak(values.to_vec().into_boxed_slice()).as_ptr()
}

fn make_resumption(code: isize, values: &[i64]) -> isize {
    let code = unsafe { std::mem::transmute::<usize, YulangCpsI64Continuation>(code as usize) };
    Box::into_raw(Box::new(YulangCpsI64Resumption {
        code,
        env: make_env(values),
    })) as isize
}

#[unsafe(no_mangle)]
pub extern "C" fn yulang_cps_make_resumption_i64_0(code: isize) -> isize {
    make_resumption(code, &[])
}

#[unsafe(no_mangle)]
pub extern "C" fn yulang_cps_make_resumption_i64_1(code: isize, a: i64) -> isize {
    make_resumption(code, &[a])
}

#[unsafe(no_mangle)]
pub extern "C" fn yulang_cps_make_resumption_i64_2(code: isize, a: i64, b: i64) -> isize {
    make_resumption(code, &[a, b])
}

#[unsafe(no_mangle)]
pub extern "C" fn yulang_cps_make_resumption_i64_3(code: isize, a: i64, b: i64, c: i64) -> isize {
    make_resumption(code, &[a, b, c])
}

#[unsafe(no_mangle)]
pub extern "C" fn yulang_cps_make_resumption_i64_4(
    code: isize,
    a: i64,
    b: i64,
    c: i64,
    d: i64,
) -> isize {
    make_resumption(code, &[a, b, c, d])
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
    unsafe { (resumption.code)(resumption.env, arg) }
}
