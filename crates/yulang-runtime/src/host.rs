use yulang_core_ir as core_ir;

use crate::vm::{VmError, VmModule, VmRequest, VmResult, VmValue};

pub struct HostRunOutput {
    pub results: Vec<VmResult>,
    pub stdout: String,
}

pub fn eval_roots_with_basic_host(module: &VmModule) -> Result<HostRunOutput, VmError> {
    let mut results = Vec::new();
    let mut stdout = String::new();

    for index in 0..module.module().root_exprs.len() {
        let result = eval_root_with_basic_host(module, index, &mut stdout)?;
        results.push(result);
    }

    Ok(HostRunOutput { results, stdout })
}

pub fn eval_root_with_basic_host(
    module: &VmModule,
    index: usize,
    stdout: &mut String,
) -> Result<VmResult, VmError> {
    let mut result = module.eval_root_expr(index)?;
    loop {
        let request = match result {
            VmResult::Value(_) => return Ok(result),
            VmResult::Request(request) if !handle_console_request(&request, stdout) => {
                return Ok(VmResult::Request(request));
            }
            VmResult::Request(request) => request,
        };
        result = module.resume_request(request, VmValue::Unit)?;
    }
}

fn handle_console_request(request: &VmRequest, stdout: &mut String) -> bool {
    if console_effect_is(&request.effect, "print") {
        stdout.push_str(&host_string(&request.payload));
        true
    } else if console_effect_is(&request.effect, "println") {
        stdout.push_str(&host_string(&request.payload));
        stdout.push('\n');
        true
    } else {
        false
    }
}

fn console_effect_is(path: &core_ir::Path, op: &str) -> bool {
    let [std, console_module, console_act, operation] = path.segments.as_slice() else {
        return false;
    };

    std.0 == "std"
        && console_module.0 == "console"
        && console_act.0 == "console"
        && operation.0 == op
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
