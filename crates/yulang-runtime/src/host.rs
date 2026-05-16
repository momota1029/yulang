use yulang_typed_ir as typed_ir;

use crate::vm::{VmError, VmModule, VmProfile, VmRequest, VmResult, VmValue};

pub struct HostRunOutput {
    pub results: Vec<VmResult>,
    pub stdout: String,
    pub vm_profile: VmProfile,
}

pub fn eval_roots_with_basic_host(module: &VmModule) -> Result<HostRunOutput, VmError> {
    let mut results = Vec::new();
    let mut stdout = String::new();
    let mut vm_profile = VmProfile::default();

    for index in 0..module.module().root_exprs.len() {
        let result = eval_root_with_basic_host(module, index, &mut stdout)?;
        vm_profile.merge(result.1);
        let result = result.0;
        results.push(result);
    }

    Ok(HostRunOutput {
        results,
        stdout,
        vm_profile,
    })
}

pub fn eval_root_with_basic_host(
    module: &VmModule,
    index: usize,
    stdout: &mut String,
) -> Result<(VmResult, VmProfile), VmError> {
    let (mut result, mut vm_profile) = module.eval_root_expr_profiled(index)?;
    loop {
        match result {
            VmResult::Value(value @ VmValue::Thunk(_)) => {
                let forced = module.force_value_profiled(value)?;
                result = forced.0;
                vm_profile.merge(forced.1);
            }
            VmResult::Value(_) => return Ok((result, vm_profile)),
            VmResult::Request(request) => {
                let Some(value) = handle_host_request(&request, stdout) else {
                    return Ok((VmResult::Request(request), vm_profile));
                };
                let resumed = module.resume_request_profiled(request, value)?;
                result = resumed.0;
                vm_profile.merge(resumed.1);
            }
        }
    }
}

fn handle_host_request(request: &VmRequest, stdout: &mut String) -> Option<VmValue> {
    handle_out_request(request, stdout)
        .or_else(|| handle_err_request(request))
        .or_else(|| handle_warn_request(request))
        .or_else(|| handle_die_request(request))
        .or_else(|| handle_debug_request(request))
        .or_else(|| handle_fs_request(request))
}

fn handle_out_request(request: &VmRequest, stdout: &mut String) -> Option<VmValue> {
    if !out_effect_is(&request.effect, "out", "write") {
        return None;
    }
    stdout.push_str(&host_string(&request.payload));
    Some(VmValue::Unit)
}

fn handle_err_request(request: &VmRequest) -> Option<VmValue> {
    if !out_effect_is(&request.effect, "err", "write") {
        return None;
    }
    eprint!("{}", host_string(&request.payload));
    Some(VmValue::Unit)
}

fn handle_warn_request(request: &VmRequest) -> Option<VmValue> {
    if !out_effect_is(&request.effect, "warn", "warn") {
        return None;
    }
    eprintln!("warning: {}", host_string(&request.payload));
    Some(VmValue::Unit)
}

fn handle_die_request(request: &VmRequest) -> Option<VmValue> {
    if !out_effect_is(&request.effect, "die", "die") {
        return None;
    }
    eprintln!("die: {}", host_string(&request.payload));
    std::process::exit(1);
}

fn out_effect_is(path: &typed_ir::Path, act: &str, op: &str) -> bool {
    let [std, mod_seg, act_seg, operation] = path.segments.as_slice() else {
        return false;
    };

    std.0 == "std" && mod_seg.0 == "out" && act_seg.0 == act && operation.0 == op
}

#[cfg(not(target_arch = "wasm32"))]
fn handle_fs_request(request: &VmRequest) -> Option<VmValue> {
    use std::fs;

    let op = fs_effect_operation(&request.effect)?;
    match op {
        "read_at" => {
            let (path, range) = host_path_range_pair(&request.payload)?;
            Some(match fs::read(path.as_ref()) {
                Ok(bytes) => host_read_at_result(&bytes, &range),
                Err(error) => host_fs_error_result(host_fs_error_code(&error)),
            })
        }
        "write_at" => {
            let (path, range, text) = host_path_range_text_triple(&request.payload)?;
            let code = match fs::read(path.as_ref()) {
                Ok(mut bytes) => {
                    let (start, end) = host_normalized_int_range(&range, bytes.len())?;
                    bytes.splice(start..end, text.as_bytes().iter().copied());
                    fs::write(path.as_ref(), bytes)
                        .err()
                        .map_or(0, |error| host_fs_error_code(&error))
                }
                Err(error) if error.kind() == std::io::ErrorKind::NotFound => {
                    fs::write(path.as_ref(), text.as_bytes())
                        .err()
                        .map_or(0, |error| host_fs_error_code(&error))
                }
                Err(error) => host_fs_error_code(&error),
            };
            Some(VmValue::Int(code.to_string()))
        }
        "read_text" => {
            let path = host_path_string(&request.payload)?;
            Some(match fs::read_to_string(path) {
                Ok(text) => host_opt_some(VmValue::String(text.into())),
                Err(_) => host_opt_none(),
            })
        }
        "write_text" => {
            let (path, text) = host_path_text_pair(&request.payload)?;
            Some(VmValue::Bool(fs::write(path, text).is_ok()))
        }
        "exists" => {
            let path = host_path_value(&request.payload)?;
            Some(VmValue::Bool(path.exists()))
        }
        "is_file" => {
            let path = host_path_value(&request.payload)?;
            Some(VmValue::Bool(path.is_file()))
        }
        "is_dir" => {
            let path = host_path_value(&request.payload)?;
            Some(VmValue::Bool(path.is_dir()))
        }
        _ => None,
    }
}

#[cfg(target_arch = "wasm32")]
fn handle_fs_request(_request: &VmRequest) -> Option<VmValue> {
    None
}

fn fs_effect_operation(path: &typed_ir::Path) -> Option<&str> {
    let [std, fs_module, fs_act, operation] = path.segments.as_slice() else {
        return None;
    };

    (std.0 == "std" && fs_module.0 == "fs" && fs_act.0 == "fs").then_some(operation.0.as_str())
}

fn handle_debug_request(request: &VmRequest) -> Option<VmValue> {
    debug_effect_is(&request.effect)
        .then(|| VmValue::String(host_debug_string(&request.payload).into()))
}

fn debug_effect_is(path: &typed_ir::Path) -> bool {
    let [std, prelude, role, method] = path.segments.as_slice() else {
        return false;
    };

    std.0 == "std" && prelude.0 == "prelude" && role.0 == "Debug" && method.0 == "debug"
}

fn host_path_string(value: &VmValue) -> Option<String> {
    match value {
        VmValue::String(value) => Some(value.to_flat_string()),
        _ => None,
    }
}

fn host_path_value(value: &VmValue) -> Option<std::rc::Rc<std::path::PathBuf>> {
    match value {
        VmValue::Path(value) => Some(value.clone()),
        VmValue::String(value) => Some(std::rc::Rc::new(std::path::PathBuf::from(
            value.to_flat_string(),
        ))),
        _ => None,
    }
}

fn host_path_range_pair(value: &VmValue) -> Option<(std::rc::Rc<std::path::PathBuf>, VmValue)> {
    let VmValue::Tuple(items) = value else {
        return None;
    };
    let [path, range] = items.as_slice() else {
        return None;
    };
    Some((host_path_value(path)?, range.clone()))
}

fn host_path_range_text_triple(
    value: &VmValue,
) -> Option<(std::rc::Rc<std::path::PathBuf>, VmValue, String)> {
    let VmValue::Tuple(items) = value else {
        return None;
    };
    let [path, range, text] = items.as_slice() else {
        return None;
    };
    Some((
        host_path_value(path)?,
        range.clone(),
        host_path_string(text)?,
    ))
}

fn host_path_text_pair(value: &VmValue) -> Option<(String, String)> {
    let VmValue::Tuple(items) = value else {
        return None;
    };
    let [path, text] = items.as_slice() else {
        return None;
    };
    Some((host_path_string(path)?, host_path_string(text)?))
}

fn host_read_at_result(bytes: &[u8], range: &VmValue) -> VmValue {
    let Some((start, end)) = host_normalized_int_range(range, bytes.len()) else {
        return host_fs_error_result(3);
    };
    let slice = &bytes[start..end];
    let valid_len = match std::str::from_utf8(slice) {
        Ok(text) => {
            return VmValue::Tuple(vec![
                VmValue::Int("0".to_string()),
                VmValue::String(text.into()),
                host_range_value(start, end),
            ]);
        }
        Err(error) => error.valid_up_to(),
    };
    let valid_end = start + valid_len;
    let text = std::str::from_utf8(&bytes[start..valid_end]).unwrap_or("");
    VmValue::Tuple(vec![
        VmValue::Int("0".to_string()),
        VmValue::String(text.into()),
        host_range_value(start, valid_end),
    ])
}

fn host_fs_error_result(code: i64) -> VmValue {
    VmValue::Tuple(vec![
        VmValue::Int(code.to_string()),
        VmValue::String("".into()),
        host_range_value(0, 0),
    ])
}

fn host_fs_error_code(error: &std::io::Error) -> i64 {
    match error.kind() {
        std::io::ErrorKind::NotFound => 1,
        std::io::ErrorKind::PermissionDenied => 2,
        _ => 3,
    }
}

fn host_normalized_int_range(value: &VmValue, len: usize) -> Option<(usize, usize)> {
    let VmValue::Variant { tag, value } = value else {
        return None;
    };
    if tag.0 != "within" {
        return None;
    }
    let VmValue::Tuple(items) = value.as_deref()? else {
        return None;
    };
    let [start, end] = items.as_slice() else {
        return None;
    };
    let start = host_normalized_start_bound(start)?;
    let end = host_normalized_end_bound(end, len)?;
    (start <= end && end <= len).then_some((start, end))
}

fn host_normalized_start_bound(value: &VmValue) -> Option<usize> {
    let VmValue::Variant { tag, value } = value else {
        return None;
    };
    match tag.0.as_str() {
        "unbounded" => Some(0),
        "included" => usize::try_from(host_bound_int(value.as_deref()?)?).ok(),
        "excluded" => usize::try_from(host_bound_int(value.as_deref()?)? + 1).ok(),
        _ => None,
    }
}

fn host_normalized_end_bound(value: &VmValue, len: usize) -> Option<usize> {
    let VmValue::Variant { tag, value } = value else {
        return None;
    };
    match tag.0.as_str() {
        "unbounded" => Some(len),
        "included" => usize::try_from(host_bound_int(value.as_deref()?)? + 1).ok(),
        "excluded" => usize::try_from(host_bound_int(value.as_deref()?)?).ok(),
        _ => None,
    }
}

fn host_bound_int(value: &VmValue) -> Option<i64> {
    match value {
        VmValue::Int(value) => value.parse().ok(),
        _ => None,
    }
}

fn host_range_value(start: usize, end: usize) -> VmValue {
    VmValue::Variant {
        tag: typed_ir::Name("within".to_string()),
        value: Some(Box::new(VmValue::Tuple(vec![
            host_bound_value("included", start),
            host_bound_value("excluded", end),
        ]))),
    }
}

fn host_bound_value(tag: &str, value: usize) -> VmValue {
    VmValue::Variant {
        tag: typed_ir::Name(tag.to_string()),
        value: Some(Box::new(VmValue::Int(value.to_string()))),
    }
}

fn host_opt_some(value: VmValue) -> VmValue {
    VmValue::Variant {
        tag: typed_ir::Name("just".to_string()),
        value: Some(Box::new(value)),
    }
}

fn host_opt_none() -> VmValue {
    VmValue::Variant {
        tag: typed_ir::Name("nil".to_string()),
        value: None,
    }
}

fn host_string(value: &VmValue) -> String {
    match value {
        VmValue::String(value) => value.to_flat_string(),
        VmValue::Int(value) | VmValue::Float(value) => value.clone(),
        VmValue::Bool(value) => value.to_string(),
        VmValue::Unit => "()".to_string(),
        VmValue::Bytes(value) => format!("<bytes len={}>", value.len()),
        VmValue::Path(value) => value.display().to_string(),
        _ => format!("{value:?}"),
    }
}

fn host_debug_string(value: &VmValue) -> String {
    match value {
        VmValue::Int(value) | VmValue::Float(value) => value.clone(),
        VmValue::String(value) => format!("{:?}", value.to_flat_string()),
        VmValue::Bytes(value) => format!("<bytes len={}>", value.len()),
        VmValue::Path(value) => format!("{:?}", value.display().to_string()),
        VmValue::Bool(value) => value.to_string(),
        VmValue::Unit => "()".to_string(),
        VmValue::List(items) => format!(
            "[{}]",
            items
                .to_vec()
                .iter()
                .map(|item| host_debug_string(item.as_ref()))
                .collect::<Vec<_>>()
                .join(", ")
        ),
        VmValue::Tuple(items) => format!(
            "({})",
            items
                .iter()
                .map(host_debug_string)
                .collect::<Vec<_>>()
                .join(", ")
        ),
        VmValue::Record(fields) => format!(
            "{{{}}}",
            fields
                .iter()
                .map(|(name, value)| format!("{}: {}", name.0, host_debug_string(value)))
                .collect::<Vec<_>>()
                .join(", ")
        ),
        VmValue::Variant { tag, value } => match value {
            Some(value) => format!("{} {}", tag.0, host_debug_string(value)),
            None => tag.0.clone(),
        },
        VmValue::EffectOp(path) => format!("<effect-op {}>", host_format_path(path)),
        VmValue::PrimitiveOp(_) => "<primitive>".to_string(),
        VmValue::Resume(_) => "<resume>".to_string(),
        VmValue::Closure(_) => "<closure>".to_string(),
        VmValue::Thunk(_) => "<thunk>".to_string(),
        VmValue::EffectId(id) => format!("<effect-id {id}>"),
    }
}

fn host_format_path(path: &typed_ir::Path) -> String {
    path.segments
        .iter()
        .map(|segment| segment.0.as_str())
        .collect::<Vec<_>>()
        .join("::")
}
