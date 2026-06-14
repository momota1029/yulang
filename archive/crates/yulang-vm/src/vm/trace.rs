use super::*;

thread_local! {
    pub(super) static HANDLE_TRACE_BUFFER: std::cell::RefCell<Vec<String>> =
        const { std::cell::RefCell::new(Vec::new()) };
}

pub(super) fn handle_trace_enabled() -> bool {
    static CACHED: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *CACHED.get_or_init(|| std::env::var("YULANG_TRACE_HANDLE").is_ok())
}

pub(super) fn trace_handle_event(tag: &str, id: u64, frames: &[Frame]) {
    if !handle_trace_enabled() {
        return;
    }
    let handle_ids: Vec<u64> = frames.iter().filter_map(frame_handle_id).collect();
    push(format!(
        "HANDLE_TRACE {tag} target_id={id} frames_len={} handle_ids={:?}",
        frames.len(),
        handle_ids
    ));
}

pub(super) fn trace_handle_push(tag: &str, id: u64, request: &VmRequest) {
    if !handle_trace_enabled() {
        return;
    }
    push(format!(
        "HANDLE_TRACE {tag} id={id} effect={:?} frames_before_push={}",
        request.effect,
        request.continuation.frames.len()
    ));
}

pub(super) fn trace_eval_var(tag: &str, path: &typed_ir::Path, value: &VmValue) {
    if !handle_trace_enabled() {
        return;
    }
    let path_str = format!("{path:?}");
    if !trace_path_contains(&path_str, &["&s#", "run", "update"]) {
        return;
    }
    let value_tag = match value {
        VmValue::Closure(c) => {
            let body_tag = expr_kind_tag(&c.body.kind);
            let self_name = c
                .self_name
                .as_ref()
                .map(|p| format!("{p:?}"))
                .unwrap_or_else(|| "<anon>".to_string());
            format!(
                "closure(self_name={self_name},body={body_tag},env_keys={})",
                c.env.len()
            )
        }
        VmValue::Thunk(t) => format!("thunk(blocked={})", t.blocked.len()),
        VmValue::EffectOp(_) => "effect_op".to_string(),
        VmValue::Resume(_) => "resume".to_string(),
        VmValue::Unit => "unit".to_string(),
        _ => "other".to_string(),
    };
    push(format!(
        "HANDLE_TRACE eval_var.{tag} path={path_str} value={value_tag}"
    ));
}

pub(super) fn trace_eval_var_binding(tag: &str, path: &typed_ir::Path) {
    if !handle_trace_enabled() {
        return;
    }
    let path_str = format!("{path:?}");
    if !trace_path_contains(&path_str, &["&s#", "run", "update"]) {
        return;
    }
    push(format!("HANDLE_TRACE eval_var.{tag} path={path_str}"));
}

pub(super) fn trace_eval_var_effect_op(tag: &str, path: &typed_ir::Path) {
    if !handle_trace_enabled() {
        return;
    }
    let path_str = format!("{path:?}");
    if !trace_path_contains(&path_str, &["set", "get", "update"]) {
        return;
    }
    push(format!("HANDLE_TRACE eval_var.{tag} path={path_str}"));
}

pub(super) fn trace_apply_eval_entry(
    tag: &str,
    callee_kind: &ExprKind,
    arg_kind: &ExprKind,
    delay_arg: bool,
) {
    if !handle_trace_enabled() {
        return;
    }
    let callee_tag = expr_kind_apply_tag(callee_kind);
    let arg_tag = expr_kind_apply_tag(arg_kind);
    push(format!(
        "HANDLE_TRACE {tag} callee_kind={callee_tag} arg_kind={arg_tag} delay_arg={delay_arg}"
    ));
}

pub(super) fn trace_apply_callee_ty(callee_kind: &ExprKind, ty: &Type) {
    if !handle_trace_enabled() {
        return;
    }
    let is_set = matches!(callee_kind, ExprKind::EffectOp(p) if format!("{p:?}").contains("set"));
    let is_run = matches!(callee_kind, ExprKind::Var(p) if format!("{p:?}").contains("run"));
    let is_apply_chain = matches!(callee_kind, ExprKind::Apply { .. });
    if !(is_set || is_run || is_apply_chain) {
        return;
    }
    push(format!(
        "HANDLE_TRACE apply_eval.callee_ty kind=brief ty={ty:?}"
    ));
}

pub(super) fn trace_apply_eval_callee_ready(callee: &VmValue) {
    if !handle_trace_enabled() {
        return;
    }
    let callee_tag = match callee {
        VmValue::Closure(c) => {
            let name = c
                .self_name
                .as_ref()
                .map(|p| format!("{p:?}"))
                .unwrap_or_else(|| "<anon>".to_string());
            let body_tag = expr_kind_tag(&c.body.kind);
            format!("closure(self_name={name},body={body_tag})")
        }
        VmValue::Thunk(_) => "thunk".to_string(),
        VmValue::EffectOp(_) => "effect_op".to_string(),
        VmValue::Resume(_) => "resume".to_string(),
        VmValue::PrimitiveOp(_) => "primitive".to_string(),
        _ => "other".to_string(),
    };
    push(format!(
        "HANDLE_TRACE apply_eval.callee_ready callee={callee_tag}"
    ));
}

pub(super) fn trace_handle_repush(tag: &str, id: u64, continuation: &VmContinuation) {
    if !handle_trace_enabled() {
        return;
    }
    push(format!(
        "HANDLE_TRACE {tag} id={id} frames_before_push={}",
        continuation.frames.len()
    ));
}

pub(super) fn trace_handle_request_outcome(tag: &str, id: u64, effect: &typed_ir::Path) {
    if !handle_trace_enabled() {
        return;
    }
    push(format!(
        "HANDLE_TRACE handle_request.{tag} id={id} effect={:?}",
        effect
    ));
}

pub(super) fn trace_handle_request_arm_miss(
    id: u64,
    effect: &typed_ir::Path,
    arm_effects: &[String],
) {
    if !handle_trace_enabled() {
        return;
    }
    push(format!(
        "HANDLE_TRACE handle_request.arm_miss id={id} effect={:?} arms={:?}",
        effect, arm_effects
    ));
}

pub(super) fn trace_propagate_entry(effect: &typed_ir::Path, before: usize, frames: &[Frame]) {
    if !handle_trace_enabled() {
        return;
    }
    let handle_ids: Vec<u64> = frames.iter().filter_map(frame_handle_id).collect();
    let blocked_count = frames
        .iter()
        .filter(|f| matches!(f, Frame::BlockedEffects { .. }))
        .count();
    push(format!(
        "HANDLE_TRACE propagate.entry effect={:?} before={} frames_len={} handle_ids={:?} blocked_count={}",
        effect,
        before,
        frames.len(),
        handle_ids,
        blocked_count
    ));
}

pub(super) fn trace_propagate_no_handler(effect: &typed_ir::Path) {
    if !handle_trace_enabled() {
        return;
    }
    push(format!(
        "HANDLE_TRACE propagate.no_handler effect={:?}",
        effect
    ));
}

pub(super) fn trace_bind_here_entry(value: &VmValue) {
    if !handle_trace_enabled() {
        return;
    }
    let tag = match value {
        VmValue::Thunk(thunk) => {
            let body_tag = match &thunk.body {
                ThunkBody::Expr(_) => "thunk_expr",
                ThunkBody::Value(_) => "thunk_value",
                ThunkBody::Emit { effect, .. } => {
                    push(format!(
                        "HANDLE_TRACE bind_here.entry value=thunk_emit effect={:?} blocked_count={}",
                        effect,
                        thunk.blocked.len()
                    ));
                    return;
                }
            };
            push(format!(
                "HANDLE_TRACE bind_here.entry value={} blocked_count={}",
                body_tag,
                thunk.blocked.len()
            ));
            return;
        }
        VmValue::Closure(_) => "closure",
        VmValue::Resume(_) => "resume",
        VmValue::EffectOp(_) => "effect_op",
        VmValue::Unit => "unit",
        _ => "other",
    };
    push(format!("HANDLE_TRACE bind_here.entry value={}", tag));
}

pub(super) fn trace_apply_entry(callee: &VmValue, arg: &VmValue) {
    if !handle_trace_enabled() {
        return;
    }
    let callee_tag = match callee {
        VmValue::Closure(c) => {
            let name = c
                .self_name
                .as_ref()
                .map(|p| format!("{p:?}"))
                .unwrap_or_else(|| "<anon>".to_string());
            let short_name = if trace_path_contains(&name, &["&s#", "run", "update", "loop"]) {
                name
            } else {
                "<other_closure>".to_string()
            };
            format!("closure({short_name})")
        }
        VmValue::Resume(_) => "resume".to_string(),
        VmValue::EffectOp(p) => format!("effect_op({p:?})"),
        VmValue::Thunk(_) => "thunk".to_string(),
        VmValue::PrimitiveOp(_) => "primitive".to_string(),
        _ => "other".to_string(),
    };
    let arg_tag = match arg {
        VmValue::Thunk(t) => format!("thunk(blocked={})", t.blocked.len()),
        VmValue::Closure(_) => "closure".to_string(),
        VmValue::Resume(_) => "resume".to_string(),
        VmValue::EffectOp(_) => "effect_op".to_string(),
        VmValue::Unit => "unit".to_string(),
        VmValue::Int(_) => "int".to_string(),
        _ => "other".to_string(),
    };
    push(format!(
        "HANDLE_TRACE apply.entry callee={} arg={}",
        callee_tag, arg_tag
    ));
}

pub(super) fn trace_continue_handle_result(
    expected_ty: &Type,
    result: &VmResult,
    continuation: &VmContinuation,
) {
    if !handle_trace_enabled() {
        return;
    }
    let expected_tag = match expected_ty {
        Type::Thunk { .. } => "thunk",
        Type::Value(_) => "value",
        Type::Unknown => "unknown",
        _ => "other",
    };
    let result_tag = match result {
        VmResult::Value(VmValue::Thunk(_)) => "value_thunk",
        VmResult::Value(_) => "value_other",
        VmResult::Request(_) => "request",
    };
    let handle_ids: Vec<u64> = continuation
        .frames
        .iter()
        .filter_map(frame_handle_id)
        .collect();
    push(format!(
        "HANDLE_TRACE continue_handle_result expected={} result={} outer_frames_len={} outer_handle_ids={:?}",
        expected_tag,
        result_tag,
        continuation.frames.len(),
        handle_ids
    ));
}

fn expr_kind_tag(kind: &ExprKind) -> &'static str {
    match kind {
        ExprKind::Lambda { .. } => "lambda",
        ExprKind::LocalPushId { .. } => "local_push_id",
        ExprKind::Handle { .. } => "handle",
        ExprKind::BindHere { .. } => "bind_here",
        ExprKind::Apply { .. } => "apply",
        ExprKind::AddId { .. } => "add_id",
        ExprKind::Thunk { .. } => "thunk_expr",
        ExprKind::Coerce { .. } => "coerce",
        _ => "other",
    }
}

fn expr_kind_apply_tag(kind: &ExprKind) -> String {
    match kind {
        ExprKind::Var(p) => format!("Var({p:?})"),
        ExprKind::EffectOp(p) => format!("EffectOp({p:?})"),
        ExprKind::Apply { .. } => "Apply".to_string(),
        ExprKind::Lambda { .. } => "Lambda".to_string(),
        ExprKind::BindHere { .. } => "BindHere".to_string(),
        ExprKind::Thunk { .. } => "Thunk".to_string(),
        ExprKind::Lit(_) => "Lit".to_string(),
        ExprKind::Coerce { .. } => "Coerce".to_string(),
        ExprKind::AddId { .. } => "AddId".to_string(),
        ExprKind::LocalPushId { .. } => "LocalPushId".to_string(),
        ExprKind::Pack { .. } => "Pack".to_string(),
        _ => "other".to_string(),
    }
}

fn frame_handle_id(frame: &Frame) -> Option<u64> {
    match frame {
        Frame::Handle { id, .. } => Some(*id),
        _ => None,
    }
}

fn trace_path_contains(path: &str, needles: &[&str]) -> bool {
    needles.iter().any(|needle| path.contains(needle))
}

fn push(line: String) {
    HANDLE_TRACE_BUFFER.with(|cell| cell.borrow_mut().push(line));
}
