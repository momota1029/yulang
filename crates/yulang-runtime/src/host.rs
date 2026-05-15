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
    handle_console_request(request, stdout)
        .or_else(|| handle_debug_request(request))
        .or_else(|| handle_fs_request(request))
}

fn handle_console_request(request: &VmRequest, stdout: &mut String) -> Option<VmValue> {
    if console_effect_is(&request.effect, "print") {
        stdout.push_str(&host_string(&request.payload));
        Some(VmValue::Unit)
    } else if console_effect_is(&request.effect, "println") {
        stdout.push_str(&host_string(&request.payload));
        stdout.push('\n');
        Some(VmValue::Unit)
    } else {
        None
    }
}

fn console_effect_is(path: &typed_ir::Path, op: &str) -> bool {
    let [std, console_module, console_act, operation] = path.segments.as_slice() else {
        return false;
    };

    std.0 == "std"
        && console_module.0 == "console"
        && console_act.0 == "console"
        && operation.0 == op
}

#[cfg(not(target_arch = "wasm32"))]
fn handle_fs_request(request: &VmRequest) -> Option<VmValue> {
    use std::fs;
    use std::path::Path;

    let op = fs_effect_operation(&request.effect)?;
    match op {
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
            let path = host_path_string(&request.payload)?;
            Some(VmValue::Bool(Path::new(&path).exists()))
        }
        "is_file" => {
            let path = host_path_string(&request.payload)?;
            Some(VmValue::Bool(Path::new(&path).is_file()))
        }
        "is_dir" => {
            let path = host_path_string(&request.payload)?;
            Some(VmValue::Bool(Path::new(&path).is_dir()))
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

fn host_path_text_pair(value: &VmValue) -> Option<(String, String)> {
    let VmValue::Tuple(items) = value else {
        return None;
    };
    let [path, text] = items.as_slice() else {
        return None;
    };
    Some((host_path_string(path)?, host_path_string(text)?))
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
        _ => format!("{value:?}"),
    }
}

fn host_debug_string(value: &VmValue) -> String {
    match value {
        VmValue::Int(value) | VmValue::Float(value) => value.clone(),
        VmValue::String(value) => format!("{:?}", value.to_flat_string()),
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
