//! Runtime value support used by native value-lane code.
//!
//! This module is the API boundary native code calls through helper symbols.
//! The initial implementation deliberately stores `VmValue` internally so the
//! native prototype shares VM semantics.  The public helper surface is small
//! enough that the storage can later move to a compact native value layout.

use std::collections::BTreeMap;
use std::io::Write;
use std::rc::Rc;

use yulang_core_ir as core_ir;
use yulang_runtime as runtime;

#[derive(Default)]
pub struct NativeRuntimeContext {
    values: Vec<Box<runtime::VmValue>>,
}

impl NativeRuntimeContext {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn alloc(&mut self, value: runtime::VmValue) -> *mut runtime::VmValue {
        self.values.push(Box::new(value));
        self.values
            .last_mut()
            .map(|value| value.as_mut() as *mut runtime::VmValue)
            .unwrap_or(std::ptr::null_mut())
    }

    pub fn clone_value(&self, value: *mut runtime::VmValue) -> Option<runtime::VmValue> {
        if value.is_null() {
            return None;
        }
        Some(unsafe { (*value).clone() })
    }
}

pub fn make_int(context: &mut NativeRuntimeContext, bytes: &[u8]) -> Option<*mut runtime::VmValue> {
    let text = std::str::from_utf8(bytes).ok()?;
    Some(context.alloc(runtime::VmValue::Int(text.to_string())))
}

pub fn make_string(
    context: &mut NativeRuntimeContext,
    bytes: &[u8],
) -> Option<*mut runtime::VmValue> {
    let text = std::str::from_utf8(bytes).ok()?;
    Some(context.alloc(runtime::VmValue::String(
        runtime::runtime::string_tree::StringTree::from_str(text),
    )))
}

pub fn make_float(
    context: &mut NativeRuntimeContext,
    bytes: &[u8],
) -> Option<*mut runtime::VmValue> {
    let text = std::str::from_utf8(bytes).ok()?;
    Some(context.alloc(runtime::VmValue::Float(text.to_string())))
}

pub fn make_bool(context: &mut NativeRuntimeContext, value: bool) -> *mut runtime::VmValue {
    context.alloc(runtime::VmValue::Bool(value))
}

pub fn make_unit(context: &mut NativeRuntimeContext) -> *mut runtime::VmValue {
    context.alloc(runtime::VmValue::Unit)
}

pub fn concat_string(
    context: &mut NativeRuntimeContext,
    left: *mut runtime::VmValue,
    right: *mut runtime::VmValue,
) -> Option<*mut runtime::VmValue> {
    let left = unsafe { left.as_ref()? };
    let right = unsafe { right.as_ref()? };
    let (runtime::VmValue::String(left), runtime::VmValue::String(right)) = (left, right) else {
        return None;
    };
    Some(context.alloc(runtime::VmValue::String(
        runtime::runtime::string_tree::StringTree::concat(left.clone(), right.clone()),
    )))
}

pub fn list_empty(context: &mut NativeRuntimeContext) -> *mut runtime::VmValue {
    context.alloc(runtime::VmValue::List(
        runtime::runtime::list_tree::ListTree::empty(),
    ))
}

pub fn list_singleton(
    context: &mut NativeRuntimeContext,
    value: *mut runtime::VmValue,
) -> Option<*mut runtime::VmValue> {
    let value = unsafe { value.as_ref()? };
    Some(context.alloc(runtime::VmValue::List(
        runtime::runtime::list_tree::ListTree::singleton(Rc::new(value.clone())),
    )))
}

pub fn list_merge(
    context: &mut NativeRuntimeContext,
    left: *mut runtime::VmValue,
    right: *mut runtime::VmValue,
) -> Option<*mut runtime::VmValue> {
    let left = unsafe { left.as_ref()? };
    let right = unsafe { right.as_ref()? };
    let (runtime::VmValue::List(left), runtime::VmValue::List(right)) = (left, right) else {
        return None;
    };
    Some(context.alloc(runtime::VmValue::List(
        runtime::runtime::list_tree::ListTree::concat(left.clone(), right.clone()),
    )))
}

pub fn list_len(
    context: &mut NativeRuntimeContext,
    list: *mut runtime::VmValue,
) -> Option<*mut runtime::VmValue> {
    let list = unsafe { list.as_ref()? };
    let runtime::VmValue::List(list) = list else {
        return None;
    };
    Some(context.alloc(runtime::VmValue::Int(list.len().to_string())))
}

pub fn list_index(
    context: &mut NativeRuntimeContext,
    list: *mut runtime::VmValue,
    index: *mut runtime::VmValue,
) -> Option<*mut runtime::VmValue> {
    let list = unsafe { list.as_ref()? };
    let index = unsafe { index.as_ref()? };
    let runtime::VmValue::List(list) = list else {
        return None;
    };
    let runtime::VmValue::Int(index) = index else {
        return None;
    };
    let index = index.parse::<usize>().ok()?;
    let value = list.index(index)?;
    Some(context.alloc(value.as_ref().clone()))
}

pub fn tuple_empty(context: &mut NativeRuntimeContext) -> *mut runtime::VmValue {
    context.alloc(runtime::VmValue::Tuple(Vec::new()))
}

pub fn tuple_push(
    context: &mut NativeRuntimeContext,
    tuple: *mut runtime::VmValue,
    value: *mut runtime::VmValue,
) -> Option<*mut runtime::VmValue> {
    let tuple = unsafe { tuple.as_ref()? };
    let value = unsafe { value.as_ref()? };
    let runtime::VmValue::Tuple(items) = tuple else {
        return None;
    };
    let mut items = items.clone();
    items.push(value.clone());
    Some(context.alloc(runtime::VmValue::Tuple(items)))
}

pub fn record_empty(context: &mut NativeRuntimeContext) -> *mut runtime::VmValue {
    context.alloc(runtime::VmValue::Record(BTreeMap::new()))
}

pub fn record_insert(
    context: &mut NativeRuntimeContext,
    record: *mut runtime::VmValue,
    name: &[u8],
    value: *mut runtime::VmValue,
) -> Option<*mut runtime::VmValue> {
    let record = unsafe { record.as_ref()? };
    let value = unsafe { value.as_ref()? };
    let runtime::VmValue::Record(fields) = record else {
        return None;
    };
    let name = std::str::from_utf8(name).ok()?;
    let mut fields = fields.clone();
    fields.insert(core_ir_name(name), value.clone());
    Some(context.alloc(runtime::VmValue::Record(fields)))
}

pub fn record_select(
    context: &mut NativeRuntimeContext,
    record: *mut runtime::VmValue,
    name: &[u8],
) -> Option<*mut runtime::VmValue> {
    let record = unsafe { record.as_ref()? };
    let runtime::VmValue::Record(fields) = record else {
        return None;
    };
    let name = std::str::from_utf8(name).ok()?;
    let value = fields.get(&core_ir_name(name))?;
    Some(context.alloc(value.clone()))
}

pub fn variant(
    context: &mut NativeRuntimeContext,
    tag: &[u8],
    value: *mut runtime::VmValue,
) -> Option<*mut runtime::VmValue> {
    let tag = std::str::from_utf8(tag).ok()?;
    let value = if value.is_null() {
        None
    } else {
        Some(Box::new(unsafe { value.as_ref()? }.clone()))
    };
    Some(context.alloc(runtime::VmValue::Variant {
        tag: core_ir_name(tag),
        value,
    }))
}

#[unsafe(no_mangle)]
pub extern "C" fn yulang_native_context_new() -> *mut NativeRuntimeContext {
    Box::into_raw(Box::new(NativeRuntimeContext::new()))
}

#[unsafe(no_mangle)]
pub extern "C" fn yulang_native_context_free(context: *mut NativeRuntimeContext) {
    if context.is_null() {
        return;
    }
    unsafe {
        drop(Box::from_raw(context));
    }
}

#[unsafe(no_mangle)]
pub extern "C" fn yulang_native_print_value(value: *mut runtime::VmValue) {
    if value.is_null() {
        print!("<null>");
        flush_stdout();
        return;
    }
    let value = unsafe { &*value };
    print_native_value(value);
    flush_stdout();
}

#[unsafe(no_mangle)]
pub extern "C" fn yulang_native_make_int(
    context: *mut NativeRuntimeContext,
    ptr: *const u8,
    len: usize,
) -> *mut runtime::VmValue {
    let Some(context) = (unsafe { context.as_mut() }) else {
        return std::ptr::null_mut();
    };
    let Some(bytes) = bytes_from_raw(ptr, len) else {
        return std::ptr::null_mut();
    };
    make_int(context, bytes).unwrap_or(std::ptr::null_mut())
}

#[unsafe(no_mangle)]
pub extern "C" fn yulang_native_make_string(
    context: *mut NativeRuntimeContext,
    ptr: *const u8,
    len: usize,
) -> *mut runtime::VmValue {
    let Some(context) = (unsafe { context.as_mut() }) else {
        return std::ptr::null_mut();
    };
    let Some(bytes) = bytes_from_raw(ptr, len) else {
        return std::ptr::null_mut();
    };
    make_string(context, bytes).unwrap_or(std::ptr::null_mut())
}

#[unsafe(no_mangle)]
pub extern "C" fn yulang_native_make_float(
    context: *mut NativeRuntimeContext,
    ptr: *const u8,
    len: usize,
) -> *mut runtime::VmValue {
    let Some(context) = (unsafe { context.as_mut() }) else {
        return std::ptr::null_mut();
    };
    let Some(bytes) = bytes_from_raw(ptr, len) else {
        return std::ptr::null_mut();
    };
    make_float(context, bytes).unwrap_or(std::ptr::null_mut())
}

#[unsafe(no_mangle)]
pub extern "C" fn yulang_native_make_bool(
    context: *mut NativeRuntimeContext,
    value: i64,
) -> *mut runtime::VmValue {
    let Some(context) = (unsafe { context.as_mut() }) else {
        return std::ptr::null_mut();
    };
    make_bool(context, value != 0)
}

#[unsafe(no_mangle)]
pub extern "C" fn yulang_native_make_unit(
    context: *mut NativeRuntimeContext,
) -> *mut runtime::VmValue {
    let Some(context) = (unsafe { context.as_mut() }) else {
        return std::ptr::null_mut();
    };
    make_unit(context)
}

#[unsafe(no_mangle)]
pub extern "C" fn yulang_native_concat_string(
    context: *mut NativeRuntimeContext,
    left: *mut runtime::VmValue,
    right: *mut runtime::VmValue,
) -> *mut runtime::VmValue {
    let Some(context) = (unsafe { context.as_mut() }) else {
        return std::ptr::null_mut();
    };
    concat_string(context, left, right).unwrap_or(std::ptr::null_mut())
}

#[unsafe(no_mangle)]
pub extern "C" fn yulang_native_list_empty(
    context: *mut NativeRuntimeContext,
) -> *mut runtime::VmValue {
    let Some(context) = (unsafe { context.as_mut() }) else {
        return std::ptr::null_mut();
    };
    list_empty(context)
}

#[unsafe(no_mangle)]
pub extern "C" fn yulang_native_list_singleton(
    context: *mut NativeRuntimeContext,
    value: *mut runtime::VmValue,
) -> *mut runtime::VmValue {
    let Some(context) = (unsafe { context.as_mut() }) else {
        return std::ptr::null_mut();
    };
    list_singleton(context, value).unwrap_or(std::ptr::null_mut())
}

#[unsafe(no_mangle)]
pub extern "C" fn yulang_native_list_merge(
    context: *mut NativeRuntimeContext,
    left: *mut runtime::VmValue,
    right: *mut runtime::VmValue,
) -> *mut runtime::VmValue {
    let Some(context) = (unsafe { context.as_mut() }) else {
        return std::ptr::null_mut();
    };
    list_merge(context, left, right).unwrap_or(std::ptr::null_mut())
}

#[unsafe(no_mangle)]
pub extern "C" fn yulang_native_list_len(
    context: *mut NativeRuntimeContext,
    list: *mut runtime::VmValue,
) -> *mut runtime::VmValue {
    let Some(context) = (unsafe { context.as_mut() }) else {
        return std::ptr::null_mut();
    };
    list_len(context, list).unwrap_or(std::ptr::null_mut())
}

#[unsafe(no_mangle)]
pub extern "C" fn yulang_native_list_index(
    context: *mut NativeRuntimeContext,
    list: *mut runtime::VmValue,
    index: *mut runtime::VmValue,
) -> *mut runtime::VmValue {
    let Some(context) = (unsafe { context.as_mut() }) else {
        return std::ptr::null_mut();
    };
    list_index(context, list, index).unwrap_or(std::ptr::null_mut())
}

#[unsafe(no_mangle)]
pub extern "C" fn yulang_native_tuple_empty(
    context: *mut NativeRuntimeContext,
) -> *mut runtime::VmValue {
    let Some(context) = (unsafe { context.as_mut() }) else {
        return std::ptr::null_mut();
    };
    tuple_empty(context)
}

#[unsafe(no_mangle)]
pub extern "C" fn yulang_native_tuple_push(
    context: *mut NativeRuntimeContext,
    tuple: *mut runtime::VmValue,
    value: *mut runtime::VmValue,
) -> *mut runtime::VmValue {
    let Some(context) = (unsafe { context.as_mut() }) else {
        return std::ptr::null_mut();
    };
    tuple_push(context, tuple, value).unwrap_or(std::ptr::null_mut())
}

#[unsafe(no_mangle)]
pub extern "C" fn yulang_native_record_empty(
    context: *mut NativeRuntimeContext,
) -> *mut runtime::VmValue {
    let Some(context) = (unsafe { context.as_mut() }) else {
        return std::ptr::null_mut();
    };
    record_empty(context)
}

#[unsafe(no_mangle)]
pub extern "C" fn yulang_native_record_insert(
    context: *mut NativeRuntimeContext,
    record: *mut runtime::VmValue,
    name_ptr: *const u8,
    name_len: usize,
    value: *mut runtime::VmValue,
) -> *mut runtime::VmValue {
    let Some(context) = (unsafe { context.as_mut() }) else {
        return std::ptr::null_mut();
    };
    let Some(name) = bytes_from_raw(name_ptr, name_len) else {
        return std::ptr::null_mut();
    };
    record_insert(context, record, name, value).unwrap_or(std::ptr::null_mut())
}

#[unsafe(no_mangle)]
pub extern "C" fn yulang_native_record_select(
    context: *mut NativeRuntimeContext,
    record: *mut runtime::VmValue,
    name_ptr: *const u8,
    name_len: usize,
) -> *mut runtime::VmValue {
    let Some(context) = (unsafe { context.as_mut() }) else {
        return std::ptr::null_mut();
    };
    let Some(name) = bytes_from_raw(name_ptr, name_len) else {
        return std::ptr::null_mut();
    };
    record_select(context, record, name).unwrap_or(std::ptr::null_mut())
}

#[unsafe(no_mangle)]
pub extern "C" fn yulang_native_variant(
    context: *mut NativeRuntimeContext,
    tag_ptr: *const u8,
    tag_len: usize,
    value: *mut runtime::VmValue,
) -> *mut runtime::VmValue {
    let Some(context) = (unsafe { context.as_mut() }) else {
        return std::ptr::null_mut();
    };
    let Some(tag) = bytes_from_raw(tag_ptr, tag_len) else {
        return std::ptr::null_mut();
    };
    variant(context, tag, value).unwrap_or(std::ptr::null_mut())
}

fn print_native_value(value: &runtime::VmValue) {
    match value {
        runtime::VmValue::Int(value) | runtime::VmValue::Float(value) => print!("{value}"),
        runtime::VmValue::String(value) => print!("{}", value.to_flat_string()),
        runtime::VmValue::Bool(value) => print!("{value}"),
        runtime::VmValue::Unit => print!("()"),
        runtime::VmValue::List(value) => {
            print!("[");
            for (index, item) in value.to_vec().into_iter().enumerate() {
                if index > 0 {
                    print!(", ");
                }
                print_native_value(item.as_ref());
            }
            print!("]");
        }
        runtime::VmValue::Tuple(items) => {
            print!("(");
            for (index, item) in items.iter().enumerate() {
                if index > 0 {
                    print!(", ");
                }
                print_native_value(item);
            }
            print!(")");
        }
        runtime::VmValue::Record(fields) => {
            print!("{{");
            for (index, (name, value)) in fields.iter().enumerate() {
                if index > 0 {
                    print!(", ");
                }
                print!("{} = ", name.0);
                print_native_value(value);
            }
            print!("}}");
        }
        runtime::VmValue::Variant { tag, value } => {
            print!(":{}", tag.0);
            if let Some(value) = value {
                print!(" ");
                print_native_value(value);
            }
        }
        other => print!("{other:?}"),
    }
}

fn core_ir_name(name: &str) -> core_ir::Name {
    core_ir::Name(name.to_string())
}

fn flush_stdout() {
    let _ = std::io::stdout().flush();
}

fn bytes_from_raw<'a>(ptr: *const u8, len: usize) -> Option<&'a [u8]> {
    if ptr.is_null() {
        return None;
    }
    Some(unsafe { std::slice::from_raw_parts(ptr, len) })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn api_builds_string_concat() {
        let mut context = NativeRuntimeContext::new();
        let left = make_string(&mut context, b"yu").expect("left");
        let right = make_string(&mut context, b"lang").expect("right");
        let value = concat_string(&mut context, left, right).expect("concat");

        let Some(runtime::VmValue::String(value)) = context.clone_value(value) else {
            panic!("expected string");
        };
        assert_eq!(value.to_flat_string(), "yulang");
    }

    #[test]
    fn api_builds_shared_vm_list() {
        let mut context = NativeRuntimeContext::new();
        let one = make_int(&mut context, b"1").expect("one");
        let two = make_int(&mut context, b"2").expect("two");
        let left = list_singleton(&mut context, one).expect("left");
        let right = list_singleton(&mut context, two).expect("right");
        let value = list_merge(&mut context, left, right).expect("merge");

        let Some(runtime::VmValue::List(value)) = context.clone_value(value) else {
            panic!("expected list");
        };
        let items = value
            .to_vec()
            .into_iter()
            .map(|value| match value.as_ref() {
                runtime::VmValue::Int(value) => value.clone(),
                other => panic!("expected int item, got {other:?}"),
            })
            .collect::<Vec<_>>();
        assert_eq!(items, ["1", "2"]);
    }

    #[test]
    fn api_indexes_list_and_reports_length() {
        let mut context = NativeRuntimeContext::new();
        let one = make_int(&mut context, b"1").expect("one");
        let two = make_int(&mut context, b"2").expect("two");
        let left = list_singleton(&mut context, one).expect("left");
        let right = list_singleton(&mut context, two).expect("right");
        let list = list_merge(&mut context, left, right).expect("merge");
        let index = make_int(&mut context, b"1").expect("index");

        let len = list_len(&mut context, list).expect("len");
        let item = list_index(&mut context, list, index).expect("index value");

        assert!(matches!(
            context.clone_value(len),
            Some(runtime::VmValue::Int(value)) if value == "2"
        ));
        assert!(matches!(
            context.clone_value(item),
            Some(runtime::VmValue::Int(value)) if value == "2"
        ));
    }
}
