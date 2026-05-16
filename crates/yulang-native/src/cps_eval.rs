use std::cell::RefCell;
use std::collections::{BTreeMap, HashSet};
use std::fmt;
use std::rc::Rc;

use yulang_runtime as runtime;
use yulang_typed_ir as typed_ir;

use crate::cps_frame_trace::{
    CpsFrameTraceEvent, CpsFrameTraceLayer, CpsFrameTraceSlot, push_cps_frame_trace_event,
};
use crate::cps_ir::{
    CpsContinuation, CpsContinuationId, CpsFunction, CpsHandlerArm, CpsHandlerEnv, CpsHandlerId,
    CpsLiteral, CpsModule, CpsStmt, CpsTerminator, CpsValueId,
};

pub type CpsEvalResult<T> = Result<T, CpsEvalError>;

thread_local! {
    static LATEST_HANDLER_ENVS: RefCell<Vec<CpsLatestHandlerEnv>> = const { RefCell::new(Vec::new()) };
}

fn trace_enabled() -> bool {
    std::env::var_os("YULANG_CPS_TRACE_FRAMES").is_some()
}

fn trace_cps(event: &str, msg: impl std::fmt::Display) {
    if trace_enabled() {
        eprintln!("[cps-trace] {event}: {msg}");
    }
}

/// Compact summary of a CpsRuntimeValue for trace output. Avoids the
/// recursive Debug bomb that thunks/closures/resumptions produce.
fn summarize_cps_value(value: &CpsRuntimeValue) -> String {
    match value {
        CpsRuntimeValue::Plain(v) => format!("Plain({v:?})"),
        CpsRuntimeValue::Thunk(thunk) => {
            format!(
                "Thunk(owner={}, entry={:?})",
                thunk.owner_function, thunk.entry
            )
        }
        CpsRuntimeValue::Closure(closure) => format!(
            "Closure(owner={}, entry={:?}, recursive_self={:?})",
            closure.owner_function, closure.entry, closure.recursive_self,
        ),
        CpsRuntimeValue::Resumption(resumption) => format!(
            "Resumption(owner={}, target={:?}, frames={}, handlers={}, guards={})",
            resumption.owner_function,
            resumption.target,
            resumption.return_frames.len(),
            resumption.handlers.len(),
            resumption.guard_stack.len(),
        ),
        CpsRuntimeValue::List(items) => {
            let preview = items
                .iter()
                .take(3)
                .map(summarize_cps_value)
                .collect::<Vec<_>>()
                .join(", ");
            format!("List(len={}, [{}])", items.len(), preview)
        }
        CpsRuntimeValue::Tuple(items) => {
            let preview = items
                .iter()
                .map(summarize_cps_value)
                .collect::<Vec<_>>()
                .join(", ");
            format!("Tuple([{preview}])")
        }
        CpsRuntimeValue::Record(fields) => {
            let preview = fields
                .iter()
                .map(|(name, value)| format!("{}: {}", name.0, summarize_cps_value(value)))
                .collect::<Vec<_>>()
                .join(", ");
            format!("Record({{{preview}}})")
        }
        CpsRuntimeValue::Variant { tag, value } => match value {
            Some(value) => format!("Variant({}, {})", tag.0, summarize_cps_value(value)),
            None => format!("Variant({})", tag.0),
        },
        CpsRuntimeValue::ScopeReturn {
            prompt,
            target,
            value,
        } => format!(
            "ScopeReturn(prompt={}, target={:?}, value={})",
            prompt.0,
            target,
            summarize_cps_value(value),
        ),
        CpsRuntimeValue::RoutedJump(jump) => format!(
            "RoutedJump(owner={}, target={:?}, value={}, threshold={})",
            jump.owner_function,
            jump.target,
            summarize_cps_value(&jump.value),
            jump.return_frame_threshold,
        ),
        CpsRuntimeValue::Aborted(value) => format!("Aborted({})", summarize_cps_value(value)),
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum CpsEvalError {
    MissingFunction {
        name: String,
    },
    MissingContinuation {
        function: String,
        id: CpsContinuationId,
    },
    MissingHandler {
        function: String,
        id: CpsHandlerId,
    },
    ContinuationArgumentMismatch {
        function: String,
        id: CpsContinuationId,
        expected: usize,
        actual: usize,
    },
    FunctionArgumentMismatch {
        function: String,
        expected: usize,
        actual: usize,
    },
    MissingValue {
        function: String,
        id: CpsValueId,
    },
    ExpectedPlainValue {
        function: String,
        id: CpsValueId,
    },
    ExpectedResumption {
        function: String,
        id: CpsValueId,
    },
    UnsupportedPrimitive {
        op: typed_ir::PrimitiveOp,
    },
    PrimitiveTypeMismatch {
        op: typed_ir::PrimitiveOp,
        value: runtime::VmValue,
    },
    InvalidPrimitiveArity {
        op: typed_ir::PrimitiveOp,
        expected: usize,
        actual: usize,
    },
    ExpectedRecord {
        function: String,
        value: runtime::VmValue,
    },
    MissingRecordField {
        function: String,
        field: typed_ir::Name,
    },
    MissingGuard,
    ExpectedGuard {
        function: String,
        id: CpsValueId,
        value: runtime::VmValue,
    },
    /// A `ScopeReturn` reached the root without ever finding its prompt
    /// in `active_handlers`. This is a lowering bug — every `Perform`
    /// must lead to an arm whose enclosing handler scope is still on
    /// the stack.
    EscapedScopeReturn {
        function: String,
        prompt: u64,
        target: CpsContinuationId,
    },
}

impl fmt::Display for CpsEvalError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            CpsEvalError::MissingFunction { name } => {
                write!(f, "CPS function {name} is missing")
            }
            CpsEvalError::MissingContinuation { function, id } => {
                write!(f, "CPS function {function} is missing continuation {id:?}")
            }
            CpsEvalError::MissingHandler { function, id } => {
                write!(f, "CPS function {function} is missing handler {id:?}")
            }
            CpsEvalError::ContinuationArgumentMismatch {
                function,
                id,
                expected,
                actual,
            } => write!(
                f,
                "CPS continuation {function}::{id:?} expected {expected} arguments, got {actual}"
            ),
            CpsEvalError::FunctionArgumentMismatch {
                function,
                expected,
                actual,
            } => write!(
                f,
                "CPS function {function} expected {expected} arguments, got {actual}"
            ),
            CpsEvalError::MissingValue { function, id } => {
                write!(f, "CPS function {function} references missing value {id:?}")
            }
            CpsEvalError::ExpectedPlainValue { function, id } => {
                write!(f, "CPS function {function} expected plain value {id:?}")
            }
            CpsEvalError::ExpectedResumption { function, id } => {
                write!(
                    f,
                    "CPS function {function} expected resumption value {id:?}"
                )
            }
            CpsEvalError::UnsupportedPrimitive { op } => {
                write!(f, "CPS evaluator does not support primitive {op:?} yet")
            }
            CpsEvalError::PrimitiveTypeMismatch { op, value } => {
                write!(f, "CPS primitive {op:?} cannot accept value {value:?}")
            }
            CpsEvalError::InvalidPrimitiveArity {
                op,
                expected,
                actual,
            } => write!(
                f,
                "CPS primitive {op:?} expected {expected} arguments, got {actual}"
            ),
            CpsEvalError::ExpectedRecord { function, value } => {
                write!(
                    f,
                    "CPS function {function} expected record value, got {value:?}"
                )
            }
            CpsEvalError::MissingRecordField { function, field } => {
                write!(
                    f,
                    "CPS function {function} selected missing record field {field:?}"
                )
            }
            CpsEvalError::MissingGuard => write!(f, "CPS evaluator has no active guard id"),
            CpsEvalError::ExpectedGuard {
                function,
                id,
                value,
            } => write!(
                f,
                "CPS function {function} expected guard value {id:?}, got {value:?}"
            ),
            CpsEvalError::EscapedScopeReturn {
                function,
                prompt,
                target,
            } => write!(
                f,
                "ScopeReturn (prompt {prompt}, target {target:?}) escaped \
                 from CPS function {function} without a matching handler"
            ),
        }
    }
}

impl std::error::Error for CpsEvalError {}

pub fn eval_cps_module(module: &CpsModule) -> CpsEvalResult<Vec<runtime::VmValue>> {
    module
        .roots
        .iter()
        .map(|root| {
            let value = with_fresh_handler_env_overlay(|| eval_function(module, root, Vec::new()))?;
            let value = resolve_routed_jump(module, value, &[])?;
            // ScopeReturn must be matched against an InstallHandler frame
            // somewhere on the way up. If one reaches the root, that's a
            // lowering bug — there was no handler to catch it.
            if let CpsRuntimeValue::ScopeReturn { prompt, target, .. } = &value {
                return Err(CpsEvalError::EscapedScopeReturn {
                    function: root.name.clone(),
                    prompt: prompt.0,
                    target: *target,
                });
            }
            into_plain_value(root, CpsValueId(usize::MAX), unwrap_aborted(value))
        })
        .collect()
}

fn with_fresh_handler_env_overlay<T>(f: impl FnOnce() -> T) -> T {
    let previous = LATEST_HANDLER_ENVS.with(|envs| envs.replace(Vec::new()));
    let result = f();
    LATEST_HANDLER_ENVS.with(|envs| {
        envs.replace(previous);
    });
    result
}

fn unwrap_aborted(value: CpsRuntimeValue) -> CpsRuntimeValue {
    match value {
        CpsRuntimeValue::Aborted(inner) => unwrap_aborted(*inner),
        other => other,
    }
}

/// Outcome of inspecting a value returned by an internal call (DirectCall,
/// ApplyClosure, ForceThunk, Resume, ResumeWithHandler) for a `ScopeReturn`
/// that should be routed by the current eval frame.
enum ScopeReturnAction {
    /// Plain value — write to the call site's `dest` and continue.
    Value(CpsRuntimeValue),
    /// `ScopeReturn`'s prompt matched a frame in `active_handlers`. The
    /// matched frame and any inner ones have already been popped. The
    /// caller should jump to `target` (with `value` as the single arg) if
    /// `target != EXIT_RWH_TARGET`, or return `value` from the current
    /// eval frame if `target == EXIT_RWH_TARGET`. `return_frame_threshold`
    /// is how many return_frames existed when the matched handler was
    /// installed; frames pushed after that count are inside the handler
    /// scope and should be discarded (delimited-continuation extent).
    JumpOrExit {
        target: CpsContinuationId,
        value: CpsRuntimeValue,
        return_frame_threshold: usize,
    },
    /// `ScopeReturn` did not match — propagate the original value up.
    Propagate(CpsRuntimeValue),
}

fn handle_scope_return(
    result: CpsRuntimeValue,
    active_handlers: &mut Vec<CpsHandlerFrame>,
    current_function: &str,
    current_eval_id: CpsEvalId,
) -> ScopeReturnAction {
    match result {
        CpsRuntimeValue::ScopeReturn {
            prompt,
            target,
            value,
        } => {
            // A ScopeReturn is resolved only by the eval frame that installed
            // the matching handler prompt. Function identity is not enough:
            // a multi-shot resumption can run the same CPS function in a
            // fresh eval frame (e.g. `each__mono1` replayed inside an outer
            // `once`'s recursive arm), and that fresh frame must not catch
            // a handler installed by the original eval. Return frames
            // preserve `owner_eval_id` so the original eval identity is
            // restored when the captured continuation is resumed via
            // `continue_return_frames` (write22).
            if let Some(index) = active_handlers.iter().rposition(|frame| {
                frame.prompt == prompt && frame.install_eval_id == current_eval_id
            }) {
                let frame = &active_handlers[index];
                // owner check: a function-local jump target only makes
                // sense in the same function. EXIT_RWH_TARGET is the
                // sentinel for ResumeWithHandler so it crosses functions.
                let frame_owner_match =
                    target == EXIT_RWH_TARGET || frame.escape_owner_function == current_function;
                let frame_owner = frame.escape_owner_function.clone();
                let frame_install_eval = frame.install_eval_id;
                let threshold = frame.return_frame_threshold;
                if !frame_owner_match {
                    trace_cps(
                        "ScopeReturnDispatch",
                        format!(
                            "fn={} eval={} prompt={} target={:?} matched=yes install_eval={} owner={} owner_match=no action=Propagate",
                            current_function,
                            current_eval_id.0,
                            prompt.0,
                            target,
                            frame_install_eval.0,
                            frame_owner,
                        ),
                    );
                    return ScopeReturnAction::Propagate(CpsRuntimeValue::ScopeReturn {
                        prompt,
                        target,
                        value,
                    });
                }
                trace_cps(
                    "ScopeReturnDispatch",
                    format!(
                        "fn={} eval={} prompt={} target={:?} matched=yes install_eval={} owner={} owner_match=yes threshold={} action=JumpOrExit",
                        current_function,
                        current_eval_id.0,
                        prompt.0,
                        target,
                        frame_install_eval.0,
                        frame_owner,
                        threshold,
                    ),
                );
                active_handlers.truncate(index);
                ScopeReturnAction::JumpOrExit {
                    target,
                    value: *value,
                    return_frame_threshold: threshold,
                }
            } else {
                trace_cps(
                    "ScopeReturnDispatch",
                    format!(
                        "fn={} eval={} prompt={} target={:?} matched=no action=Propagate",
                        current_function, current_eval_id.0, prompt.0, target,
                    ),
                );
                ScopeReturnAction::Propagate(CpsRuntimeValue::ScopeReturn {
                    prompt,
                    target,
                    value,
                })
            }
        }
        other => ScopeReturnAction::Value(other),
    }
}

/// Mark every handler frame as inherited so a fresh `eval_continuations`
/// frame doesn't try to resolve a `ScopeReturn` against handlers whose
/// real install site lives in a parent eval.
fn into_inherited(mut handlers: Vec<CpsHandlerFrame>) -> Vec<CpsHandlerFrame> {
    for frame in &mut handlers {
        frame.inherited = true;
    }
    handlers
}

fn cps_value_from_vm(value: runtime::VmValue) -> CpsRuntimeValue {
    match value {
        runtime::VmValue::Tuple(items) => {
            CpsRuntimeValue::Tuple(items.into_iter().map(cps_value_from_vm).collect())
        }
        runtime::VmValue::Variant { tag, value } => CpsRuntimeValue::Variant {
            tag,
            value: value.map(|v| Box::new(cps_value_from_vm(*v))),
        },
        runtime::VmValue::List(list) => {
            let items = list
                .to_vec()
                .into_iter()
                .map(|item| cps_value_from_vm((*item).clone()))
                .collect::<Vec<_>>();
            CpsRuntimeValue::List(Rc::new(items))
        }
        other => CpsRuntimeValue::Plain(other),
    }
}

fn cps_value_to_vm(value: CpsRuntimeValue) -> Option<runtime::VmValue> {
    match value {
        CpsRuntimeValue::Plain(value) => Some(value),
        CpsRuntimeValue::Aborted(inner) => cps_value_to_vm(*inner),
        CpsRuntimeValue::RoutedJump(_) => None,
        // ScopeReturn must never appear here — callers either resolve it via
        // `handle_scope_return` at every internal call boundary, or fail at
        // root with EscapedScopeReturn. Returning None lets `into_plain_value`
        // surface ExpectedPlainValue if it does sneak through.
        CpsRuntimeValue::ScopeReturn { .. } => None,
        CpsRuntimeValue::Tuple(items) => Some(runtime::VmValue::Tuple(
            items
                .into_iter()
                .map(cps_value_to_vm)
                .collect::<Option<Vec<_>>>()?,
        )),
        CpsRuntimeValue::Record(fields) => Some(runtime::VmValue::Record(
            fields
                .into_iter()
                .map(|(name, value)| Some((name, cps_value_to_vm(value)?)))
                .collect::<Option<BTreeMap<_, _>>>()?,
        )),
        CpsRuntimeValue::Variant { tag, value } => Some(runtime::VmValue::Variant {
            tag,
            value: match value {
                Some(value) => Some(Box::new(cps_value_to_vm(*value)?)),
                None => None,
            },
        }),
        CpsRuntimeValue::List(items) => {
            let vm_items = items
                .iter()
                .cloned()
                .map(cps_value_to_vm)
                .collect::<Option<Vec<_>>>()?;
            let mut tree = runtime::runtime::list_tree::ListTree::empty();
            for item in vm_items {
                tree = runtime::runtime::list_tree::ListTree::concat(
                    tree,
                    runtime::runtime::list_tree::ListTree::singleton(Rc::new(item)),
                );
            }
            Some(runtime::VmValue::List(tree))
        }
        CpsRuntimeValue::Resumption(_)
        | CpsRuntimeValue::Thunk(_)
        | CpsRuntimeValue::Closure(_) => None,
    }
}

fn eval_function(
    module: &CpsModule,
    function: &CpsFunction,
    args: Vec<runtime::VmValue>,
) -> CpsEvalResult<CpsRuntimeValue> {
    eval_function_with_context(
        module,
        function,
        args.into_iter().map(CpsRuntimeValue::Plain).collect(),
        Vec::new(),
        Vec::new(),
        Vec::new(),
        Vec::new(),
        0,
    )
}

fn eval_function_with_context(
    module: &CpsModule,
    function: &CpsFunction,
    args: Vec<CpsRuntimeValue>,
    active_handlers: Vec<CpsHandlerFrame>,
    guard_stack: Vec<CpsGuardEntry>,
    return_frames: Vec<CpsReturnFrame>,
    active_blocked: Vec<CpsBlockedEffect>,
    initial_frame_count: usize,
) -> CpsEvalResult<CpsRuntimeValue> {
    if function.params.len() != args.len() {
        return Err(CpsEvalError::FunctionArgumentMismatch {
            function: function.name.clone(),
            expected: function.params.len(),
            actual: args.len(),
        });
    }
    // Inherit all handler frames from the caller so this fresh eval does not
    // resolve ScopeReturns that belong to parent scopes.
    eval_continuations(
        module,
        function,
        function.entry,
        args,
        Vec::new(),
        active_handlers,
        guard_stack,
        return_frames,
        active_blocked,
        initial_frame_count,
    )
}

/// Entry point that inherits caller handlers before entering the loop.
/// Use this for cross-function calls (direct calls, closure applies, thunk forces).
/// Issues a fresh `CpsEvalId` — this eval is a new dynamic frame, so any
/// handler installed inside it gets a fresh `install_eval_id` and any
/// ScopeReturn raised inside it can only resolve handlers installed here.
fn eval_continuations(
    module: &CpsModule,
    function: &CpsFunction,
    entry: CpsContinuationId,
    initial_args: Vec<CpsRuntimeValue>,
    initial_values: Vec<Option<CpsRuntimeValue>>,
    active_handlers: Vec<CpsHandlerFrame>,
    guard_stack: Vec<CpsGuardEntry>,
    return_frames: Vec<CpsReturnFrame>,
    active_blocked: Vec<CpsBlockedEffect>,
    initial_frame_count: usize,
) -> CpsEvalResult<CpsRuntimeValue> {
    let current_eval_id = fresh_eval_id();
    resume_continuation(
        module,
        function,
        entry,
        initial_args,
        initial_values,
        into_inherited(active_handlers),
        guard_stack,
        return_frames,
        active_blocked,
        initial_frame_count,
        current_eval_id,
    )
}

/// Core evaluation loop. Unlike `eval_continuations`, does NOT call
/// `into_inherited` and does NOT issue a fresh eval id — the caller is
/// responsible for handler state and for choosing the eval identity. Used
/// by `continue_return_frames` so restored frames see their handlers with
/// the original inherited/non-inherited state preserved AND with the
/// original owner eval id restored as `current_eval_id` (write22).
fn resume_continuation(
    module: &CpsModule,
    function: &CpsFunction,
    entry: CpsContinuationId,
    initial_args: Vec<CpsRuntimeValue>,
    initial_values: Vec<Option<CpsRuntimeValue>>,
    active_handlers: Vec<CpsHandlerFrame>,
    guard_stack: Vec<CpsGuardEntry>,
    return_frames: Vec<CpsReturnFrame>,
    active_blocked: Vec<CpsBlockedEffect>,
    initial_frame_count: usize,
    current_eval_id: CpsEvalId,
) -> CpsEvalResult<CpsRuntimeValue> {
    let mut values = initial_values;
    let mut current = entry;
    let mut args = initial_args;
    let mut guard_stack = guard_stack;
    let mut active_handlers = active_handlers;
    let mut return_frames = return_frames;
    let active_blocked = active_blocked;
    let initial_frame_count = initial_frame_count;
    let current_eval_id = current_eval_id;
    let mut next_guard_id = guard_stack
        .iter()
        .map(|entry| entry.id)
        .max()
        .map_or(0, |id| id + 1);
    // Loop labels are hygienic across macros; pass the label explicitly.
    macro_rules! dispatch_scope_return {
        ($cont:lifetime, $result:expr, $dest:expr) => {{
            let result = resolve_routed_jump(module, $result, &return_frames)?;
            if matches!(
                result,
                CpsRuntimeValue::Aborted(_) | CpsRuntimeValue::RoutedJump(_)
            ) {
                return Ok(result);
            }
            match handle_scope_return(
                result,
                &mut active_handlers,
                &function.name,
                current_eval_id,
            ) {
                // Plain value or EXIT-target match: the value belongs to
                // the call site's `dest` slot, and execution of the rest
                // of the current continuation continues normally.
                ScopeReturnAction::Value(v) => write_value(&mut values, *$dest, v),
                ScopeReturnAction::JumpOrExit { target, value, return_frame_threshold }
                    if target == EXIT_RWH_TARGET =>
                {
                    // Cut frames installed inside the matched handler's scope.
                    if return_frames.len() > return_frame_threshold {
                        return_frames.truncate(return_frame_threshold);
                    }
                    write_value(&mut values, *$dest, value);
                }
                ScopeReturnAction::JumpOrExit { target, value, return_frame_threshold } => {
                    if return_frames.len() > return_frame_threshold {
                        return_frames.truncate(return_frame_threshold);
                    }
                    current = target;
                    args = vec![value];
                    continue $cont;
                }
                ScopeReturnAction::Propagate(v) => {
                    // write25 Step 5: before bubbling the SR via the
                    // call stack, see if the current eval's own
                    // return_frames hold the install scope for this
                    // handler (e.g. a Resume eval's adjusted captured
                    // chain). If so, route there directly with the
                    // modified active_handlers snapshot in scope.
                    if let Some(routed) =
                        try_route_scope_return_through_return_frames(
                            module,
                            &v,
                            &return_frames,
                            initial_frame_count,
                        )?
                    {
                        return Ok(routed);
                    }
                    return Ok(v);
                }
            }
        }};
    }
    'cont: loop {
        let continuation = continuation_by_id(function, current)?;
        assign_continuation_args(&mut values, function, continuation, args)?;
        args = Vec::new();

        for stmt in &continuation.stmts {
            match stmt {
                CpsStmt::Literal { dest, literal } => {
                    write_value(
                        &mut values,
                        *dest,
                        CpsRuntimeValue::Plain(eval_literal(literal)),
                    );
                }
                CpsStmt::FreshGuard { dest, var } => {
                    let id = next_guard_id;
                    next_guard_id += 1;
                    guard_stack.push(CpsGuardEntry { var: *var, id });
                    write_value(
                        &mut values,
                        *dest,
                        CpsRuntimeValue::Plain(runtime::VmValue::EffectId(id)),
                    );
                }
                CpsStmt::PeekGuard { dest } => {
                    let id = guard_stack
                        .last()
                        .map(|entry| entry.id)
                        .ok_or(CpsEvalError::MissingGuard)?;
                    write_value(
                        &mut values,
                        *dest,
                        CpsRuntimeValue::Plain(runtime::VmValue::EffectId(id)),
                    );
                }
                CpsStmt::FindGuard { dest, guard } => {
                    let guard = read_effect_id(function, &values, *guard)?;
                    write_value(
                        &mut values,
                        *dest,
                        CpsRuntimeValue::Plain(runtime::VmValue::Bool(
                            guard_stack.iter().any(|entry| entry.id == guard),
                        )),
                    );
                }
                CpsStmt::MakeThunk { dest, entry } => {
                    let thunk_values = values.clone();
                    write_value(
                        &mut values,
                        *dest,
                        CpsRuntimeValue::Thunk(Rc::new(CpsThunk {
                            owner_function: function.name.clone(),
                            entry: *entry,
                            values: Rc::new(thunk_values),
                            handlers: Rc::new(active_handlers.clone()),
                            guard_stack: Rc::new(guard_stack.clone()),
                            blocked: Rc::new(Vec::new()),
                        })),
                    );
                }
                CpsStmt::AddThunkBoundary {
                    dest,
                    thunk,
                    guard,
                    allowed,
                    active,
                } => {
                    let guard = read_effect_id(function, &values, *guard)?;
                    let value = add_thunk_boundary(
                        read_value(function, &values, *thunk)?,
                        guard,
                        allowed.clone(),
                        *active,
                    );
                    write_value(&mut values, *dest, value);
                }
                CpsStmt::MakeClosure { dest, entry } => {
                    let closure_values = values.clone();
                    write_value(
                        &mut values,
                        *dest,
                        CpsRuntimeValue::Closure(Rc::new(CpsClosure {
                            owner_function: function.name.clone(),
                            entry: *entry,
                            values: Rc::new(closure_values),
                            recursive_self: None,
                        })),
                    );
                }
                CpsStmt::MakeRecursiveClosure { dest, entry } => {
                    let closure_values = values.clone();
                    let closure = CpsRuntimeValue::Closure(Rc::new(CpsClosure {
                        owner_function: function.name.clone(),
                        entry: *entry,
                        values: Rc::new(closure_values),
                        recursive_self: Some(*dest),
                    }));
                    write_value(&mut values, *dest, closure);
                }
                CpsStmt::ForceThunk { dest, thunk } => {
                    // Force iteratively: a function whose body builds a
                    // `MakeThunk` (e.g. `my work(): int = { ... }` with an
                    // effect-typed return) returns a Thunk wrapping its
                    // body, and the surrounding lowering may have wrapped
                    // the call again to defer evaluation past the catch
                    // boundary. The user-level demand here is "produce the
                    // catch scope's value", which means peeling Thunks
                    // until we land on a non-Thunk (or a ScopeReturn that
                    // dispatches us elsewhere).
                    let mut result = read_value(function, &values, *thunk)?;
                    loop {
                        match result {
                            CpsRuntimeValue::Thunk(thunk) => {
                                let handlers = if !active_handlers.is_empty() {
                                    active_handlers.clone()
                                } else {
                                    thunk.handlers.as_ref().clone()
                                };
                                let guards = if !guard_stack.is_empty() {
                                    guard_stack.clone()
                                } else {
                                    thunk.guard_stack.as_ref().clone()
                                };
                                let owner = function_by_name(module, &thunk.owner_function)?;
                                // Synchronous force: inherit parent's frames
                                // so any Perform inside the thunk body
                                // captures them, but don't consume them on
                                // the thunk's plain Return (parent's eval is
                                // still alive).
                                let inherited = return_frames.len();
                                result = eval_continuations(
                                    module,
                                    owner,
                                    thunk.entry,
                                    Vec::new(),
                                    thunk.values.as_ref().clone(),
                                    handlers,
                                    guards,
                                    return_frames.clone(),
                                    active_blocked_for_thunk(&active_blocked, &thunk),
                                    inherited,
                                )?;
                                if matches!(result, CpsRuntimeValue::ScopeReturn { .. }) {
                                    break;
                                }
                            }
                            _ => break,
                        }
                    }
                    dispatch_scope_return!('cont, result, dest);
                }
                CpsStmt::Tuple { dest, items } => {
                    let items = items
                        .iter()
                        .map(|id| read_value(function, &values, *id))
                        .collect::<CpsEvalResult<Vec<_>>>()?;
                    write_value(&mut values, *dest, CpsRuntimeValue::Tuple(items));
                }
                CpsStmt::Record { dest, base, fields } => {
                    let mut record = match base {
                        Some(base) => match read_value(function, &values, *base)? {
                            CpsRuntimeValue::Record(fields) => fields,
                            CpsRuntimeValue::Plain(runtime::VmValue::Record(fields)) => fields
                                .into_iter()
                                .map(|(name, value)| (name, CpsRuntimeValue::Plain(value)))
                                .collect(),
                            value => {
                                return Err(CpsEvalError::ExpectedRecord {
                                    function: function.name.clone(),
                                    value: into_plain_value(function, *base, value)?,
                                });
                            }
                        },
                        None => BTreeMap::new(),
                    };
                    for field in fields {
                        record.insert(
                            field.name.clone(),
                            read_value(function, &values, field.value)?,
                        );
                    }
                    write_value(&mut values, *dest, CpsRuntimeValue::Record(record));
                }
                CpsStmt::RecordWithoutFields { dest, base, fields } => {
                    let mut record = match read_value(function, &values, *base)? {
                        CpsRuntimeValue::Record(fields) => fields,
                        CpsRuntimeValue::Plain(runtime::VmValue::Record(fields)) => fields
                            .into_iter()
                            .map(|(name, value)| (name, CpsRuntimeValue::Plain(value)))
                            .collect(),
                        value => {
                            return Err(CpsEvalError::ExpectedRecord {
                                function: function.name.clone(),
                                value: into_plain_value(function, *base, value)?,
                            });
                        }
                    };
                    for field in fields {
                        record.remove(field);
                    }
                    write_value(&mut values, *dest, CpsRuntimeValue::Record(record));
                }
                CpsStmt::Variant { dest, tag, value } => {
                    let value = value
                        .map(|id| read_value(function, &values, id))
                        .transpose()?
                        .map(Box::new);
                    write_value(
                        &mut values,
                        *dest,
                        CpsRuntimeValue::Variant {
                            tag: tag.clone(),
                            value,
                        },
                    );
                }
                CpsStmt::Select { dest, base, field } => {
                    let value = match read_value(function, &values, *base)? {
                        CpsRuntimeValue::Record(fields) => {
                            fields.get(field).cloned().ok_or_else(|| {
                                CpsEvalError::MissingRecordField {
                                    function: function.name.clone(),
                                    field: field.clone(),
                                }
                            })?
                        }
                        CpsRuntimeValue::Plain(runtime::VmValue::Record(fields)) => fields
                            .get(field)
                            .cloned()
                            .map(CpsRuntimeValue::Plain)
                            .ok_or_else(|| CpsEvalError::MissingRecordField {
                                function: function.name.clone(),
                                field: field.clone(),
                            })?,
                        value => {
                            return Err(CpsEvalError::ExpectedRecord {
                                function: function.name.clone(),
                                value: into_plain_value(function, *base, value)?,
                            });
                        }
                    };
                    write_value(&mut values, *dest, value);
                }
                CpsStmt::TupleGet { dest, tuple, index } => {
                    let value = match read_value(function, &values, *tuple)? {
                        CpsRuntimeValue::Tuple(items) => {
                            items.get(*index).cloned().ok_or_else(|| {
                                CpsEvalError::MissingRecordField {
                                    function: function.name.clone(),
                                    field: typed_ir::Name(index.to_string()),
                                }
                            })?
                        }
                        CpsRuntimeValue::Plain(runtime::VmValue::Tuple(items)) => {
                            cps_value_from_vm(items.get(*index).cloned().ok_or_else(|| {
                                CpsEvalError::MissingRecordField {
                                    function: function.name.clone(),
                                    field: typed_ir::Name(index.to_string()),
                                }
                            })?)
                        }
                        other => other,
                    };
                    write_value(&mut values, *dest, value);
                }
                CpsStmt::SelectWithDefault {
                    dest,
                    base,
                    field,
                    default,
                } => {
                    let default = read_value(function, &values, *default)?;
                    let value = match read_value(function, &values, *base)? {
                        CpsRuntimeValue::Record(fields) => fields.get(field).cloned(),
                        CpsRuntimeValue::Plain(runtime::VmValue::Record(fields)) => {
                            fields.get(field).cloned().map(CpsRuntimeValue::Plain)
                        }
                        value => {
                            return Err(CpsEvalError::ExpectedRecord {
                                function: function.name.clone(),
                                value: into_plain_value(function, *base, value)?,
                            });
                        }
                    }
                    .unwrap_or(default);
                    write_value(&mut values, *dest, value);
                }
                CpsStmt::RecordHasField { dest, base, field } => {
                    let has_field = match read_value(function, &values, *base)? {
                        CpsRuntimeValue::Record(fields) => fields.contains_key(field),
                        CpsRuntimeValue::Plain(runtime::VmValue::Record(fields)) => {
                            fields.contains_key(field)
                        }
                        value => {
                            return Err(CpsEvalError::ExpectedRecord {
                                function: function.name.clone(),
                                value: into_plain_value(function, *base, value)?,
                            });
                        }
                    };
                    write_value(
                        &mut values,
                        *dest,
                        CpsRuntimeValue::Plain(runtime::VmValue::Bool(has_field)),
                    );
                }
                CpsStmt::VariantTagEq { dest, variant, tag } => {
                    let matches = match read_value(function, &values, *variant)? {
                        CpsRuntimeValue::Variant { tag: actual, .. } => actual == *tag,
                        CpsRuntimeValue::Plain(runtime::VmValue::Variant {
                            tag: actual, ..
                        }) => actual == *tag,
                        _ => false,
                    };
                    write_value(
                        &mut values,
                        *dest,
                        CpsRuntimeValue::Plain(runtime::VmValue::Bool(matches)),
                    );
                }
                CpsStmt::VariantPayload { dest, variant } => {
                    let value = match read_value(function, &values, *variant)? {
                        CpsRuntimeValue::Variant {
                            value: Some(value), ..
                        } => *value,
                        CpsRuntimeValue::Variant { value: None, .. } => {
                            CpsRuntimeValue::Plain(runtime::VmValue::Unit)
                        }
                        CpsRuntimeValue::Plain(runtime::VmValue::Variant {
                            value: Some(value),
                            ..
                        }) => cps_value_from_vm(*value),
                        CpsRuntimeValue::Plain(runtime::VmValue::Variant {
                            value: None, ..
                        }) => CpsRuntimeValue::Plain(runtime::VmValue::Unit),
                        other => other,
                    };
                    write_value(&mut values, *dest, value);
                }
                CpsStmt::Primitive { dest, op, args } => {
                    let arg_values = args
                        .iter()
                        .map(|id| read_value(function, &values, *id))
                        .collect::<CpsEvalResult<Vec<_>>>()?;
                    let result = eval_cps_primitive(*op, arg_values.clone())?;
                    // Trace list-family primitives: queue manipulation is
                    // the central concern for std::undet.once's branch arm.
                    if matches!(
                        op,
                        typed_ir::PrimitiveOp::ListEmpty
                            | typed_ir::PrimitiveOp::ListSingleton
                            | typed_ir::PrimitiveOp::ListMerge
                            | typed_ir::PrimitiveOp::ListLen
                            | typed_ir::PrimitiveOp::ListIndex
                            | typed_ir::PrimitiveOp::ListIndexRangeRaw
                    ) {
                        trace_cps(
                            "PrimitiveList",
                            format!(
                                "fn={} cont={:?} op={:?} args=[{}] result={}",
                                function.name,
                                current,
                                op,
                                arg_values
                                    .iter()
                                    .map(summarize_cps_value)
                                    .collect::<Vec<_>>()
                                    .join(", "),
                                summarize_cps_value(&result),
                            ),
                        );
                    }
                    write_value(&mut values, *dest, result);
                }
                CpsStmt::DirectCall {
                    dest,
                    target,
                    args: arg_ids,
                } => {
                    let target_function = function_by_name(module, target)?;
                    let call_args = arg_ids
                        .iter()
                        .map(|id| read_value(function, &values, *id))
                        .collect::<CpsEvalResult<Vec<_>>>()?;
                    // Synchronous call: pass parent's return_frames so a
                    // Perform inside the callee captures them in the
                    // resumption. The callee's initial_frame_count = current
                    // return_frames.len() so its Return doesn't consume any
                    // (the parent eval is still alive).
                    let inherited = return_frames.len();
                    let result = eval_function_with_context(
                        module,
                        target_function,
                        call_args,
                        active_handlers.clone(),
                        guard_stack.clone(),
                        return_frames.clone(),
                        active_blocked.clone(),
                        inherited,
                    )?;
                    dispatch_scope_return!('cont, result, dest);
                }
                CpsStmt::ApplyClosure { dest, closure, arg } => {
                    // ApplyClosure can target either a Closure or a Resumption.
                    // The latter happens when a resumption was stored inside a
                    // first-class value (e.g. queue<resumption> from std::undet.once)
                    // and later extracted via TupleGet/ListIndex; the surface
                    // type system cannot distinguish them so we dispatch here.
                    let callable = read_value(function, &values, *closure)?;
                    let arg_preview = read_value(function, &values, *arg)
                        .ok()
                        .as_ref()
                        .map(summarize_cps_value)
                        .unwrap_or_else(|| "?".to_string());
                    trace_cps(
                        "ApplyClosure",
                        format!(
                            "fn={} cont={:?} callable={} arg={} return_frames.len={} initial={}",
                            function.name,
                            current,
                            summarize_cps_value(&callable),
                            arg_preview,
                            return_frames.len(),
                            initial_frame_count,
                        ),
                    );
                    let result = match callable {
                        CpsRuntimeValue::Closure(closure) => {
                            let arg = read_value(function, &values, *arg)?;
                            let owner = function_by_name(module, &closure.owner_function)?;
                            let mut closure_values = closure.values.as_ref().clone();
                            if let Some(self_id) = closure.recursive_self {
                                write_value(
                                    &mut closure_values,
                                    self_id,
                                    CpsRuntimeValue::Closure(closure.clone()),
                                );
                            }
                            // Sync apply: inherit parent's frames so a Perform
                            // inside the closure body captures them, but
                            // initial_frame_count = current len so the
                            // closure's Return doesn't consume them.
                            let inherited = return_frames.len();
                            eval_continuations(
                                module,
                                owner,
                                closure.entry,
                                vec![arg],
                                closure_values,
                                active_handlers.clone(),
                                guard_stack.clone(),
                                return_frames.clone(),
                                active_blocked.clone(),
                                inherited,
                            )?
                        }
                        CpsRuntimeValue::Resumption(resumption) => {
                            // Treat as Resume: the surface saw an opaque
                            // callable, but the runtime value is a captured
                            // continuation. Resume needs a plain payload.
                            let arg = read_plain_value(function, &values, *arg)?;
                            let owner = function_by_name(module, &resumption.owner_function)?;
                            let anchor = resumption.handled_anchor;
                            let resumed_handlers = merge_resumption_handlers(
                                resumption.handlers.as_ref(),
                                &active_handlers,
                                anchor,
                            );
                            let adjusted_frames = merge_extras_into_frames(
                                resumption.return_frames.as_ref(),
                                &active_handlers,
                                anchor,
                            );
                            trace_cps(
                                "ResumeHandlerMerge",
                                format!(
                                    "site=ApplyClosure(Resumption) fn={} eval={} anchor={:?} captured={} current={} merged={}",
                                    function.name,
                                    current_eval_id.0,
                                    anchor.map(|a| (a.prompt.0, a.install_eval_id.0)),
                                    summarize_handler_stack(resumption.handlers.as_ref()),
                                    summarize_handler_stack(&active_handlers),
                                    summarize_handler_stack(&resumed_handlers),
                                ),
                            );
                            // Resume replays a captured continuation, so the
                            // captured frames are ours to consume — initial=0.
                            eval_continuations(
                                module,
                                owner,
                                resumption.target,
                                vec![CpsRuntimeValue::Plain(arg)],
                                resumption.values.as_ref().clone(),
                                resumed_handlers,
                                resumption.guard_stack.as_ref().clone(),
                                adjusted_frames,
                                resumption.active_blocked.as_ref().clone(),
                                0,
                            )?
                        }
                        _ => {
                            return Err(CpsEvalError::ExpectedPlainValue {
                                function: function.name.clone(),
                                id: *closure,
                            });
                        }
                    };
                    dispatch_scope_return!('cont, result, dest);
                }
                CpsStmt::CloneContinuation { dest, source } => {
                    let value = read_value(function, &values, *source)?;
                    write_value(&mut values, *dest, value);
                }
                CpsStmt::Resume {
                    dest,
                    resumption,
                    arg,
                } => {
                    let resumption = read_resumption(function, &values, *resumption)?;
                    let arg = read_plain_value(function, &values, *arg)?;
                    let owner = function_by_name(module, &resumption.owner_function)?;
                    let anchor = resumption.handled_anchor;
                    let resumed_handlers = merge_resumption_handlers(
                        resumption.handlers.as_ref(),
                        &active_handlers,
                        anchor,
                    );
                    let adjusted_frames = merge_extras_into_frames(
                        resumption.return_frames.as_ref(),
                        &active_handlers,
                        anchor,
                    );
                    trace_cps(
                        "ResumeHandlerMerge",
                        format!(
                            "site=Resume fn={} eval={} anchor={:?} captured={} current={} merged={}",
                            function.name,
                            current_eval_id.0,
                            anchor.map(|a| (a.prompt.0, a.install_eval_id.0)),
                            summarize_handler_stack(resumption.handlers.as_ref()),
                            summarize_handler_stack(&active_handlers),
                            summarize_handler_stack(&resumed_handlers),
                        ),
                    );
                    // Resume replays captured continuation; captured frames
                    // are ours to consume.
                    let result = eval_continuations(
                        module,
                        owner,
                        resumption.target,
                        vec![CpsRuntimeValue::Plain(arg)],
                        resumption.values.as_ref().clone(),
                        resumed_handlers,
                        resumption.guard_stack.as_ref().clone(),
                        adjusted_frames,
                        resumption.active_blocked.as_ref().clone(),
                        0,
                    )?;
                    dispatch_scope_return!('cont, result, dest);
                }
                CpsStmt::InstallHandler {
                    handler,
                    envs,
                    value,
                    escape,
                } => {
                    let envs = capture_handler_envs(function, &values, envs)?;
                    let pushed_prompt = fresh_prompt();
                    let threshold = return_frames.len();
                    active_handlers.push(CpsHandlerFrame {
                        prompt: pushed_prompt,
                        handler: *handler,
                        guard_stack: guard_stack.clone(),
                        envs: envs.clone(),
                        escape: *escape,
                        escape_owner_function: function.name.clone(),
                        inherited: false,
                        return_frame_threshold: threshold,
                        install_eval_id: current_eval_id,
                    });
                    return_frames.push(CpsReturnFrame {
                        prompt_exit: Some(CpsPromptExitFrame {
                            prompt: pushed_prompt,
                        }),
                        owner_function: function.name.clone(),
                        continuation: *value,
                        values: Rc::new(values.clone()),
                        active_handlers: active_handlers.clone(),
                        guard_stack: guard_stack.clone(),
                        active_blocked: active_blocked.clone(),
                        owner_initial_frame_count: initial_frame_count,
                        owner_eval_id: current_eval_id,
                    });
                    trace_cps(
                        "InstallHandler",
                        format!(
                            "fn={} eval={} cont={:?} handler={:?} prompt={} value={:?} escape={:?} threshold={} handlers.now={}",
                            function.name,
                            current_eval_id.0,
                            current,
                            handler,
                            pushed_prompt.0,
                            value,
                            escape,
                            threshold,
                            active_handlers.len(),
                        ),
                    );
                }
                CpsStmt::UninstallHandler { handler } => {
                    if let Some(pos) = active_handlers
                        .iter()
                        .rposition(|frame| frame.handler == *handler)
                    {
                        active_handlers.remove(pos);
                    }
                }
                CpsStmt::ResumeWithHandler {
                    dest,
                    resumption,
                    arg,
                    handler,
                    envs,
                } => {
                    let resumption = read_resumption(function, &values, *resumption)?;
                    let arg = read_plain_value(function, &values, *arg)?;
                    let updates_existing_handler_env =
                        envs.iter().any(|env| !env.targets.is_empty());
                    let envs = capture_handler_envs(function, &values, envs)?;
                    let owner = function_by_name(module, &resumption.owner_function)?;
                    let rebase_existing_handler_env = updates_existing_handler_env
                        && resumption
                            .handlers
                            .iter()
                            .any(|frame| frame.handler == *handler);
                    overlay_handler_envs_in_stack(
                        &function.name,
                        &mut active_handlers,
                        *handler,
                        &envs,
                        true,
                    );
                    // Push the RWH-installed frame onto our own active_handlers
                    // (non-inherited, sentinel-target) so a ScopeReturn that
                    // matches the freshly-installed handler resolves at this
                    // very call site rather than escaping the eval frame.
                    let pushed_prompt = fresh_prompt();
                    if !rebase_existing_handler_env {
                        active_handlers.push(CpsHandlerFrame {
                            prompt: pushed_prompt,
                            handler: *handler,
                            guard_stack: guard_stack.clone(),
                            envs: envs.clone(),
                            escape: EXIT_RWH_TARGET,
                            escape_owner_function: function.name.clone(),
                            inherited: false,
                            return_frame_threshold: return_frames.len(),
                            install_eval_id: current_eval_id,
                        });
                    }
                    // RWH uses REBASED semantics: the just-installed handler
                    // SHADOWS the captured innermost handler. So inner_handlers
                    // = captured ++ [RWH-pushed], with RWH innermost. This is
                    // different from regular Resume merge (which preserves
                    // captured innermost). Tested by
                    // `evaluates_resumption_under_fresh_handler_stack`.
                    let inner_handlers = {
                        let mut stack = resumption.handlers.as_ref().clone();
                        overlay_handler_envs_in_stack(
                            &function.name,
                            &mut stack,
                            *handler,
                            &envs,
                            false,
                        );
                        if !rebase_existing_handler_env {
                            let mut owned = active_handlers
                                .last()
                                .cloned()
                                .expect("just pushed RWH frame");
                            owned.inherited = true;
                            stack.push(owned);
                        }
                        stack
                    };
                    let pushed_extra = if rebase_existing_handler_env {
                        Vec::new()
                    } else {
                        active_handlers
                            .iter()
                            .filter(|f| f.prompt == pushed_prompt)
                            .cloned()
                            .collect::<Vec<_>>()
                    };
                    // Frame continuations use the same rebased stack: append
                    // the RWH frame as the innermost handler for every captured
                    // return frame.
                    let mut captured_frames = resumption.return_frames.as_ref().clone();
                    overlay_handler_envs_in_frames(
                        &function.name,
                        &mut captured_frames,
                        *handler,
                        &envs,
                        false,
                    );
                    let adjusted_frames =
                        append_resume_with_handler_frames(&captured_frames, &pushed_extra);
                    let adjusted_frames = if rebase_existing_handler_env {
                        own_captured_return_frames(adjusted_frames)
                    } else {
                        adjusted_frames
                    };
                    trace_cps(
                        "ResumeHandlerMerge",
                        format!(
                            "site=ResumeWithHandler(rebased) fn={} eval={} pushed_prompt={} captured={} pushed_extra={} inner={}",
                            function.name,
                            current_eval_id.0,
                            pushed_prompt.0,
                            summarize_handler_stack(resumption.handlers.as_ref()),
                            summarize_handler_stack(&pushed_extra),
                            summarize_handler_stack(&inner_handlers),
                        ),
                    );
                    let result = eval_continuations(
                        module,
                        owner,
                        resumption.target,
                        vec![CpsRuntimeValue::Plain(arg)],
                        resumption.values.as_ref().clone(),
                        inner_handlers,
                        resumption.guard_stack.as_ref().clone(),
                        adjusted_frames,
                        resumption.active_blocked.as_ref().clone(),
                        0,
                    )?;
                    dispatch_scope_return!('cont, result, dest);
                    // Pop the RWH frame in the value-flow path. JumpOrExit /
                    // Propagate paths do not return to here, so they don't
                    // need it; an `EXIT_RWH_TARGET` match will already have
                    // truncated past this frame in `handle_scope_return`.
                    if let Some(pos) = active_handlers
                        .iter()
                        .rposition(|f| f.prompt == pushed_prompt)
                    {
                        active_handlers.truncate(pos);
                    }
                }
            }
        }

        match &continuation.terminator {
            CpsTerminator::Return(value) => {
                // Only consume frames pushed during THIS eval. The prefix up to
                // `initial_frame_count` was inherited from a sync caller and
                // belongs to that caller's eval loop, which is still alive.
                let v = read_value(function, &values, *value)?;
                trace_cps(
                    "Return",
                    format!(
                        "fn={} cont={:?} value={} return_frames.len={} initial={}",
                        function.name,
                        current,
                        summarize_cps_value(&v),
                        return_frames.len(),
                        initial_frame_count,
                    ),
                );
                if return_frames.len() <= initial_frame_count {
                    return Ok(v);
                }
                // write25 Step 5+: re-enable write17-style pre-force.
                // If the Returned value is a Thunk and the top own-frame's
                // continuation immediately ForceThunks its param, run that
                // continuation in the top frame's owner context with the
                // top frame STILL in `return_frames`. This keeps frames
                // like `F_each_post` in scope while the deferred body
                // runs, so a deep `Perform` captures them in the
                // resumption. Combined with write22's `install_eval_id`
                // and write25's walk-based routing, the captured
                // `F_each_post` lets `try_route_scope_return_through_return_frames`
                // resolve `H_sub` at its install eval directly from the
                // captured chain, instead of dropping it via call-stack
                // propagation.
                //
                // Owner check (write17's reason for being disabled):
                // running the top frame's continuation under the frame's
                // owner function avoids the previous mismatch where the
                // resumed body used `current_function=fold_impl` while
                // looking for `H_sub.escape_owner=each`. Now we run in
                // `frame.owner_function=each`, so the strict eval-id
                // check (write22) succeeds.
                if let CpsRuntimeValue::Thunk(thunk) = &v {
                    let top_index = return_frames.len() - 1;
                    let top_frame = &return_frames[top_index];
                    if return_frame_immediately_forces_param(module, top_frame)?
                        && top_index >= initial_frame_count
                    {
                        let top_frame = top_frame.clone();
                        trace_cps(
                            "PreForceResumeTopFrame",
                            format!(
                                "top_owner={} top_owner_eval={} top_cont={:?} retained_frames_len={}",
                                top_frame.owner_function,
                                top_frame.owner_eval_id.0,
                                top_frame.continuation,
                                return_frames.len(),
                            ),
                        );
                        let forced = force_returned_thunk_before_frame_consumption(
                            module,
                            thunk.clone(),
                            &top_frame,
                            return_frames.clone(),
                            initial_frame_count,
                        )?;
                        if matches!(forced, CpsRuntimeValue::ScopeReturn { .. }) {
                            return Ok(forced);
                        }
                        return continue_return_frames(module, forced, &return_frames, &[]);
                    }
                }
                // write23: pass the FULL return_frames (not just own_frames)
                // so continue_return_frames can preserve the inherited prefix
                // for the resumed eval. Previously, splitting off own_frames
                // dropped the inherited part, which silently lost the
                // parent's `F_each_post`-style frames in tail-call chains
                // (where the parent has already terminated via EffectfulCall
                // and its frames live only in the callee's return_frames).
                return continue_return_frames(module, v, &return_frames, &[]);
            }
            CpsTerminator::Continue { target, args: next } => {
                args = next
                    .iter()
                    .map(|id| read_value(function, &values, *id))
                    .collect::<CpsEvalResult<Vec<_>>>()?;
                current = *target;
            }
            CpsTerminator::Branch {
                cond,
                then_cont,
                else_cont,
            } => {
                let cond = read_plain_value(function, &values, *cond)?;
                current = if bool_value(typed_ir::PrimitiveOp::BoolNot, &cond)? {
                    *then_cont
                } else {
                    *else_cont
                };
            }
            CpsTerminator::Perform {
                effect,
                payload,
                resume,
                handler,
                blocked,
            } => {
                trace_cps(
                    "Perform",
                    format!(
                        "fn={} eval={} cont={:?} effect={:?} return_frames.len={} initial={} active_handlers={}",
                        function.name,
                        current_eval_id.0,
                        current,
                        effect,
                        return_frames.len(),
                        initial_frame_count,
                        summarize_handler_stack(&active_handlers),
                    ),
                );
                let payload = read_plain_value(function, &values, *payload)?;
                let blocked = blocked
                    .map(|blocked| read_effect_id(function, &values, blocked))
                    .transpose()?
                    .or_else(|| active_blocked_id(effect, &active_blocked));
                let handler_stack =
                    handler_stack_with_static(&active_handlers, *handler, &guard_stack);
                let (handler_arm, frame, handler_body_stack, handler_owner) =
                    handler_arm_for_stack(module, function, &handler_stack, effect, blocked)?;
                let handler_values = values_with_handler_env(
                    &handler_owner.name,
                    Vec::new(),
                    frame,
                    handler_arm.entry,
                );
                let frame_prompt = frame.prompt;
                let frame_escape = frame.escape;
                let frame_in_active = active_handlers.iter().any(|f| f.prompt == frame_prompt);
                // write24: record which handler frame's arm produced this
                // resumption. When the resumption is later resumed, merge
                // uses this as the anchor to place resume-site siblings
                // immediately after the captured handler.
                let handled_anchor = if frame_in_active {
                    Some(CpsHandlerAnchor {
                        prompt: frame.prompt,
                        install_eval_id: frame.install_eval_id,
                    })
                } else {
                    None
                };
                if trace_enabled() {
                    let matched_index = handler_stack.iter().position(|f| f.prompt == frame_prompt);
                    trace_cps(
                        "PerformHandlerSearch",
                        format!(
                            "fn={} eval={} effect={:?} stack={} matched_index={:?} matched_prompt={} matched_install_eval={} matched_owner={} in_active={}",
                            function.name,
                            current_eval_id.0,
                            effect,
                            summarize_handler_stack(&handler_stack),
                            matched_index,
                            frame.prompt.0,
                            frame.install_eval_id.0,
                            if frame.escape_owner_function.is_empty() {
                                "<synth>"
                            } else {
                                frame.escape_owner_function.as_str()
                            },
                            frame_in_active,
                        ),
                    );
                }
                let (resumption_handlers, resumption_return_frames) = if frame_in_active {
                    let captured =
                        capture_continuation_inside_prompt(&handler_stack, &return_frames, frame);
                    (captured.handlers, captured.return_frames)
                } else {
                    (handler_stack.clone(), return_frames.clone())
                };
                let resumption = CpsRuntimeValue::Resumption(Rc::new(CpsResumption {
                    owner_function: function.name.clone(),
                    target: *resume,
                    values: Rc::new(values.clone()),
                    handlers: Rc::new(resumption_handlers),
                    guard_stack: Rc::new(guard_stack.clone()),
                    active_blocked: Rc::new(active_blocked.clone()),
                    return_frames: Rc::new(resumption_return_frames),
                    handled_anchor,
                }));
                // Detect whether the chosen handler frame is in our local
                // `active_handlers` (so its prompt will match on dispatch)
                // or whether it was synthesized by `handler_stack_with_static`
                // because we had no installed handlers at all. In the
                // synthetic case the arm's result must just become the
                // perform-frame's return value, with no ScopeReturn wrapping.
                let result = eval_continuations(
                    module,
                    handler_owner,
                    handler_arm.entry,
                    vec![CpsRuntimeValue::Plain(payload), resumption],
                    handler_values,
                    handler_body_stack,
                    guard_stack.clone(),
                    Vec::new(),
                    active_blocked.clone(),
                    0,
                )?;
                if !frame_in_active {
                    // Synthetic fallback frame: the perform's effect had no
                    // installed handler in this eval, so the arm's result is
                    // the value of *this* eval frame.
                    return Ok(result);
                }
                let arm_already_reached_escape = handler_arm_continues_to_installed_escape(
                    handler_owner,
                    frame.handler,
                    handler_arm.entry,
                    frame_escape,
                );
                if arm_already_reached_escape
                    && !matches!(result, CpsRuntimeValue::ScopeReturn { .. })
                    && frame.install_eval_id == current_eval_id
                {
                    let mut frames = return_frames.clone();
                    if frames.len() > frame.return_frame_threshold {
                        frames.truncate(frame.return_frame_threshold);
                    }
                    return continue_return_frames(module, result, &frames, &[]);
                }
                if !matches!(result, CpsRuntimeValue::ScopeReturn { .. })
                    && frame.install_eval_id != current_eval_id
                    && handler_arm_uses_resume_with_handler(
                        handler_owner,
                        frame.handler,
                        handler_arm.entry,
                    )
                {
                    return Ok(result);
                }
                // The arm body's natural Return becomes a non-local jump to
                // the matching handler scope. Don't re-wrap if the arm itself
                // emitted a ScopeReturn (it might be targeting an outer scope).
                let scope_return = match result {
                    CpsRuntimeValue::ScopeReturn { .. } => result,
                    other => CpsRuntimeValue::ScopeReturn {
                        prompt: frame_prompt,
                        target: frame_escape,
                        value: Box::new(other),
                    },
                };
                // The InstallHandler that matches this perform might be in
                // the *current* function (e.g. `catch x: branch -> ...` and
                // the perform of `branch()` is in the same function). In
                // that case the prompt is in our `active_handlers` and we
                // must resolve here rather than bubble out — otherwise the
                // ScopeReturn escapes to the root.
                match handle_scope_return(
                    scope_return,
                    &mut active_handlers,
                    &function.name,
                    current_eval_id,
                ) {
                    ScopeReturnAction::Value(v) => {
                        // Shouldn't happen — we just constructed a ScopeReturn.
                        return Ok(v);
                    }
                    ScopeReturnAction::Propagate(v) => {
                        // write25 Step 5: walk own return_frames for an
                        // install-scope match before bubbling up.
                        if let Some(routed) = try_route_scope_return_through_return_frames(
                            module,
                            &v,
                            &return_frames,
                            initial_frame_count,
                        )? {
                            return Ok(routed);
                        }
                        return Ok(v);
                    }
                    ScopeReturnAction::JumpOrExit {
                        target,
                        value,
                        return_frame_threshold,
                    } => {
                        if return_frames.len() > return_frame_threshold {
                            return_frames.truncate(return_frame_threshold);
                        }
                        if target == EXIT_RWH_TARGET {
                            return Ok(value);
                        }
                        current = target;
                        args = vec![value];
                        continue 'cont;
                    }
                }
            }
            CpsTerminator::EffectfulCall {
                target,
                args: arg_ids,
                resume,
            } => {
                // Effectful direct call: this eval frame terminates here.
                // Push a return frame so the callee's Perform (or any further
                // effectful call) captures this function's post-call cont in
                // its resumption. The callee's `initial_frame_count` is the
                // pre-push length so it can consume the frame we just pushed
                // (and any further frames it pushes itself), but NOT the
                // frames we inherited from above (those remain ours-to-keep
                // until we ourselves are restored via continue_return_frames).
                let target_function = function_by_name(module, target)?;
                let call_args = arg_ids
                    .iter()
                    .map(|id| read_value(function, &values, *id))
                    .collect::<CpsEvalResult<Vec<_>>>()?;
                let pre_push_count = return_frames.len();
                let frame = CpsReturnFrame {
                    prompt_exit: None,
                    owner_function: function.name.clone(),
                    continuation: *resume,
                    values: Rc::new(values.clone()),
                    active_handlers: active_handlers.clone(),
                    guard_stack: guard_stack.clone(),
                    active_blocked: active_blocked.clone(),
                    owner_initial_frame_count: initial_frame_count,
                    owner_eval_id: current_eval_id,
                };
                let mut new_frames = return_frames.clone();
                new_frames.push(frame);
                return eval_function_with_context(
                    module,
                    target_function,
                    call_args,
                    active_handlers.clone(),
                    guard_stack.clone(),
                    new_frames,
                    active_blocked.clone(),
                    pre_push_count,
                );
            }
            CpsTerminator::EffectfulForce { thunk, resume } => {
                // Effectful thunk force: this eval frame terminates here.
                // The thunk's body runs as if called via EffectfulCall, with
                // the post-force cont captured as a return frame.
                let value = read_value(function, &values, *thunk)?;
                match value {
                    CpsRuntimeValue::Thunk(thunk_rc) => {
                        let pre_push_count = return_frames.len();
                        let frame = CpsReturnFrame {
                            prompt_exit: None,
                            owner_function: function.name.clone(),
                            continuation: *resume,
                            values: Rc::new(values.clone()),
                            active_handlers: active_handlers.clone(),
                            guard_stack: guard_stack.clone(),
                            active_blocked: active_blocked.clone(),
                            owner_initial_frame_count: initial_frame_count,
                            owner_eval_id: current_eval_id,
                        };
                        let mut new_frames = return_frames.clone();
                        new_frames.push(frame);
                        let owner = function_by_name(module, &thunk_rc.owner_function)?;
                        let handlers = if !active_handlers.is_empty() {
                            active_handlers.clone()
                        } else {
                            thunk_rc.handlers.as_ref().clone()
                        };
                        let guards = if !guard_stack.is_empty() {
                            guard_stack.clone()
                        } else {
                            thunk_rc.guard_stack.as_ref().clone()
                        };
                        return eval_continuations(
                            module,
                            owner,
                            thunk_rc.entry,
                            Vec::new(),
                            thunk_rc.values.as_ref().clone(),
                            handlers,
                            guards,
                            new_frames,
                            active_blocked_for_thunk(&active_blocked, &thunk_rc),
                            pre_push_count,
                        );
                    }
                    other => {
                        // Non-thunk value: no force needed. Pass directly to
                        // the resume continuation as if EffectfulForce was a
                        // no-op.
                        current = *resume;
                        args = vec![other];
                        continue 'cont;
                    }
                }
            }
            CpsTerminator::EffectfulApply {
                closure,
                arg,
                resume,
            } => {
                // Effectful closure application: same shape as EffectfulCall
                // but dispatches on Closure or Resumption value.
                let callable = read_value(function, &values, *closure)?;
                let arg_preview = read_value(function, &values, *arg)
                    .ok()
                    .as_ref()
                    .map(summarize_cps_value)
                    .unwrap_or_else(|| "?".to_string());
                trace_cps(
                    "EffectfulApply",
                    format!(
                        "fn={} cont={:?} callable={} arg={} resume={:?} return_frames.len={} initial={}",
                        function.name,
                        current,
                        summarize_cps_value(&callable),
                        arg_preview,
                        resume,
                        return_frames.len(),
                        initial_frame_count,
                    ),
                );
                let pre_push_count = return_frames.len();
                let frame = CpsReturnFrame {
                    prompt_exit: None,
                    owner_function: function.name.clone(),
                    continuation: *resume,
                    values: Rc::new(values.clone()),
                    active_handlers: active_handlers.clone(),
                    guard_stack: guard_stack.clone(),
                    active_blocked: active_blocked.clone(),
                    owner_initial_frame_count: initial_frame_count,
                    owner_eval_id: current_eval_id,
                };
                let mut new_frames = return_frames.clone();
                new_frames.push(frame);
                match callable {
                    CpsRuntimeValue::Closure(closure) => {
                        let arg = read_value(function, &values, *arg)?;
                        let owner = function_by_name(module, &closure.owner_function)?;
                        let mut closure_values = closure.values.as_ref().clone();
                        if let Some(self_id) = closure.recursive_self {
                            write_value(
                                &mut closure_values,
                                self_id,
                                CpsRuntimeValue::Closure(closure.clone()),
                            );
                        }
                        return eval_continuations(
                            module,
                            owner,
                            closure.entry,
                            vec![arg],
                            closure_values,
                            active_handlers.clone(),
                            guard_stack.clone(),
                            new_frames,
                            active_blocked.clone(),
                            pre_push_count,
                        );
                    }
                    CpsRuntimeValue::Resumption(resumption) => {
                        // EffectfulApply to a Resumption — replay the
                        // captured continuation, then run the post-apply
                        // cont after it returns. write16 §5: frame order
                        // matters. continue_return_frames pops from end
                        // (innermost first), so:
                        //   [parent_frames..., F_post, res_frames...]
                        // ensures consumption is:
                        //   innermost res frame → outermost res frame →
                        //   F_post → innermost parent → outermost parent.
                        let arg = read_plain_value(function, &values, *arg)?;
                        let owner = function_by_name(module, &resumption.owner_function)?;
                        let anchor = resumption.handled_anchor;
                        let resumed_handlers = merge_resumption_handlers(
                            resumption.handlers.as_ref(),
                            &active_handlers,
                            anchor,
                        );
                        let adjusted_res = merge_extras_into_frames(
                            resumption.return_frames.as_ref(),
                            &active_handlers,
                            anchor,
                        );
                        trace_cps(
                            "ResumeHandlerMerge",
                            format!(
                                "site=EffectfulApply(Resumption) fn={} eval={} anchor={:?} captured={} current={} merged={}",
                                function.name,
                                current_eval_id.0,
                                anchor.map(|a| (a.prompt.0, a.install_eval_id.0)),
                                summarize_handler_stack(resumption.handlers.as_ref()),
                                summarize_handler_stack(&active_handlers),
                                summarize_handler_stack(&resumed_handlers),
                            ),
                        );
                        // new_frames = parent_frames + [F_post]. Append
                        // adjusted_res AFTER so it pops first.
                        let mut combined_frames = new_frames;
                        combined_frames.extend(adjusted_res);
                        // Resume-style replay: captured frames are ours to
                        // consume — initial=0.
                        return eval_continuations(
                            module,
                            owner,
                            resumption.target,
                            vec![CpsRuntimeValue::Plain(arg)],
                            resumption.values.as_ref().clone(),
                            resumed_handlers,
                            resumption.guard_stack.as_ref().clone(),
                            combined_frames,
                            resumption.active_blocked.as_ref().clone(),
                            0,
                        );
                    }
                    _ => {
                        return Err(CpsEvalError::ExpectedPlainValue {
                            function: function.name.clone(),
                            id: *closure,
                        });
                    }
                }
            }
        }
    }
}

/// write17: returns true when the frame's continuation immediately
/// ForceThunks its received parameter — i.e. its first stmt is
/// `ForceThunk { thunk: <params[0]>, .. }`. Used by `Return(Thunk)` to
/// detect the case where popping the frame would lose the post-call cont
/// from a thunk body's resumption.
fn return_frame_immediately_forces_param(
    module: &CpsModule,
    frame: &CpsReturnFrame,
) -> CpsEvalResult<bool> {
    let function = function_by_name(module, &frame.owner_function)?;
    let Some(continuation) = function
        .continuations
        .iter()
        .find(|c| c.id == frame.continuation)
    else {
        return Ok(false);
    };
    let Some(&first_param) = continuation.params.first() else {
        return Ok(false);
    };
    Ok(matches!(
        continuation.stmts.first(),
        Some(CpsStmt::ForceThunk { thunk, .. }) if *thunk == first_param
    ))
}

/// write17: Evaluate a Thunk body BEFORE popping the top return frame,
/// so the body's effects can capture the frame in their resumptions.
///
/// Critical invariants:
/// - `return_frames` is passed AS-IS (no pop). The top frame stays available
///   so the thunk body's Perform sees it as captureable.
/// - `initial_frame_count` is the CURRENT eval's initial — NOT
///   `return_frames.len()`. Setting it to `len()` would make the top frame
///   inherited from the thunk body's POV and prevent it from ever being
///   consumed.
/// - handlers / guards come from `top_frame` (the would-be ForceThunk
///   context), since we're pre-empting that context.
/// - If the thunk body itself returns a Thunk, peel via loop (mirrors the
///   sync stmt-level ForceThunk's behavior).
#[allow(dead_code)]
fn force_returned_thunk_before_frame_consumption(
    module: &CpsModule,
    mut thunk: Rc<CpsThunk>,
    top_frame: &CpsReturnFrame,
    return_frames: Vec<CpsReturnFrame>,
    initial_frame_count: usize,
) -> CpsEvalResult<CpsRuntimeValue> {
    loop {
        let owner = function_by_name(module, &thunk.owner_function)?;
        // Use top_frame's saved handlers (preserving non-inherited state) and
        // resume_continuation (no into_inherited). This way an effect handler
        // installed at the EffectfulCall site (e.g. H_sub in each) remains
        // non-inherited in the body's eval, so its ScopeReturn can resolve
        // when propagating back here instead of escaping to root.
        let result = resume_continuation(
            module,
            owner,
            thunk.entry,
            Vec::new(),
            thunk.values.as_ref().clone(),
            top_frame.active_handlers.clone(),
            top_frame.guard_stack.clone(),
            return_frames.clone(),
            active_blocked_for_thunk(&top_frame.active_blocked, &thunk),
            initial_frame_count,
            // Restore the eval id of the would-be ForceThunk context so the
            // body's ScopeReturn resolves at the installer's eval.
            top_frame.owner_eval_id,
        )?;
        match result {
            CpsRuntimeValue::Thunk(next) => {
                thunk = next;
                continue;
            }
            other => return Ok(other),
        }
    }
}

/// Compact trace summary of a handler stack. Shows the key fields used by
/// ScopeReturn resolution so the trace audit can confirm merge order.
fn summarize_handler_stack(stack: &[CpsHandlerFrame]) -> String {
    let parts: Vec<String> = stack
        .iter()
        .map(|h| {
            format!(
                "(p={},inh={},eval={},owner={},thr={})",
                h.prompt.0,
                if h.inherited { "T" } else { "F" },
                h.install_eval_id.0,
                if h.escape_owner_function.is_empty() {
                    "<synth>"
                } else {
                    h.escape_owner_function.as_str()
                },
                h.return_frame_threshold,
            )
        })
        .collect();
    format!("[{}]", parts.join(","))
}

/// Are two handler frames the "same" handler — i.e. same install instance?
fn same_handler_frame(a: &CpsHandlerFrame, b: &CpsHandlerFrame) -> bool {
    a.prompt == b.prompt && a.install_eval_id == b.install_eval_id
}

fn capture_continuation_inside_prompt(
    handlers: &[CpsHandlerFrame],
    return_frames: &[CpsReturnFrame],
    handled: &CpsHandlerFrame,
) -> CapturedPromptContinuation {
    let start = captured_prompt_frame_start(return_frames, handled);
    let return_frames = return_frames[start..]
        .iter()
        .cloned()
        .map(|frame| rebase_captured_return_frame(frame, start))
        .collect();
    CapturedPromptContinuation {
        handlers: handlers
            .iter()
            .cloned()
            .map(|handler| rebase_captured_handler_frame(handler, start))
            .collect(),
        return_frames: own_captured_return_frames(return_frames),
    }
}

fn captured_prompt_frame_start(
    return_frames: &[CpsReturnFrame],
    handled: &CpsHandlerFrame,
) -> usize {
    let start = return_frames
        .iter()
        .rposition(|frame| {
            frame
                .prompt_exit
                .as_ref()
                .is_some_and(|exit| exit.prompt == handled.prompt)
        })
        .map(|index| index + 1)
        .unwrap_or(handled.return_frame_threshold)
        .min(return_frames.len());
    start
}

fn rebase_captured_return_frame(
    mut frame: CpsReturnFrame,
    dropped_frames: usize,
) -> CpsReturnFrame {
    frame.owner_initial_frame_count = frame
        .owner_initial_frame_count
        .saturating_sub(dropped_frames);
    frame.active_handlers = frame
        .active_handlers
        .into_iter()
        .map(|handler| rebase_captured_handler_frame(handler, dropped_frames))
        .collect();
    frame
}

fn rebase_captured_handler_frame(
    mut handler: CpsHandlerFrame,
    dropped_frames: usize,
) -> CpsHandlerFrame {
    handler.return_frame_threshold = handler
        .return_frame_threshold
        .saturating_sub(dropped_frames);
    handler
}

/// Merge a captured continuation's handler stack with the resume site's
/// current handler stack.
///
/// Semantics (write24): handlers installed at the resume site (in the
/// arm body) are siblings to the captured continuation's outer scope —
/// they belong AFTER the handler whose arm produced the resumption (the
/// "anchor") but BEFORE the captured continuation's inner handler tail.
/// Concretely:
///
/// ```text
/// captured = [outer, H_sub]              (e.g. branch perform capture)
/// current  = [H_inner]                   (recursive once installed H_inner)
/// anchor   = outer                       (= the captured handler that matched)
/// merged   = [outer, H_inner, H_sub]
/// ```
///
/// `handle_scope_return` uses `rposition` for handler search, so the
/// merged stack reads outer→inner (innermost = last). Putting `H_inner`
/// AFTER `outer` and BEFORE `H_sub` gives the expected semantics: a
/// new `reject` performed in the resumed continuation finds `H_inner`
/// before `outer`, and `sub::return` still aborts to `H_sub` first.
///
/// Without anchor, falls back to a shared-prefix merge: handlers in
/// `current` that aren't already in `captured` are placed before the
/// captured tail.
fn merge_resumption_handlers(
    captured: &[CpsHandlerFrame],
    current: &[CpsHandlerFrame],
    anchor: Option<CpsHandlerAnchor>,
) -> Vec<CpsHandlerFrame> {
    let is_anchor = |frame: &CpsHandlerFrame, anchor: CpsHandlerAnchor| {
        frame.prompt == anchor.prompt && frame.install_eval_id == anchor.install_eval_id
    };

    if let Some(anchor) = anchor {
        if let Some(anchor_index) = captured.iter().position(|f| is_anchor(f, anchor)) {
            let mut merged = Vec::with_capacity(captured.len() + current.len());

            // Captured prefix up to and including the anchor (the handler
            // whose arm body produced this resumption).
            merged.extend(captured[..=anchor_index].iter().cloned());

            // Resume-site siblings: handlers in `current` that aren't
            // already in the merged prefix or the captured tail. These
            // were installed in the arm body and belong between the
            // anchor and the captured tail.
            for frame in current {
                let in_prefix = merged.iter().any(|m| same_handler_frame(m, frame));
                let in_tail = captured[anchor_index + 1..]
                    .iter()
                    .any(|c| same_handler_frame(c, frame));
                if !in_prefix && !in_tail {
                    merged.push(frame.clone());
                }
            }

            // Captured continuation's inner handler tail.
            merged.extend(captured[anchor_index + 1..].iter().cloned());
            return merged;
        }
    }

    // Fallback: shared-prefix merge. Used when anchor is None
    // (synthetic-handler perform) or when the anchor handler can't be
    // located in `captured` (defensive — shouldn't happen).
    let mut shared = 0;
    while shared < captured.len()
        && shared < current.len()
        && same_handler_frame(&captured[shared], &current[shared])
    {
        shared += 1;
    }

    let mut merged = Vec::with_capacity(captured.len() + current.len());
    merged.extend(captured[..shared].iter().cloned());

    for frame in &current[shared..] {
        if !captured.iter().any(|c| same_handler_frame(c, frame)) {
            merged.push(frame.clone());
        }
    }

    merged.extend(captured[shared..].iter().cloned());
    merged
}

/// Apply `ResumeWithHandler`'s rebased handler stack to captured return frames.
///
/// The just-installed RWH frame is appended to each captured frame's handler
/// stack as the innermost handler. This intentionally differs from
/// `merge_extras_into_frames`, which preserves the captured innermost handler.
fn append_resume_with_handler_frames(
    frames: &[CpsReturnFrame],
    extra: &[CpsHandlerFrame],
) -> Vec<CpsReturnFrame> {
    if extra.is_empty() {
        return frames.to_vec();
    }
    frames
        .iter()
        .map(|frame| {
            let mut adjusted = frame.clone();
            for handler in extra {
                if !adjusted
                    .active_handlers
                    .iter()
                    .any(|h| h.prompt == handler.prompt)
                {
                    adjusted.active_handlers.push(handler.clone());
                }
            }
            adjusted
        })
        .collect()
}

/// Apply `merge_resumption_handlers` per frame: each captured return
/// frame's saved `active_handlers` is the "captured" side; `current` is
/// the resume site's live handler stack. The `anchor` (the matched
/// handler whose arm produced the resumption) is used to position the
/// resume-site siblings consistently across every captured frame.
fn merge_extras_into_frames(
    frames: &[CpsReturnFrame],
    current: &[CpsHandlerFrame],
    anchor: Option<CpsHandlerAnchor>,
) -> Vec<CpsReturnFrame> {
    frames
        .iter()
        .map(|frame| {
            let merged =
                merge_resumption_handlers(&frame.active_handlers, current, anchor);
            if trace_enabled() && merged != frame.active_handlers {
                trace_cps(
                    "InjectExtraHandlers",
                    format!(
                        "frame_owner={} frame_owner_eval={} before={} current={} anchor={:?} after={}",
                        frame.owner_function,
                        frame.owner_eval_id.0,
                        summarize_handler_stack(&frame.active_handlers),
                        summarize_handler_stack(current),
                        anchor.map(|a| (a.prompt.0, a.install_eval_id.0)),
                        summarize_handler_stack(&merged),
                    ),
                );
            }
            let mut adjusted = frame.clone();
            adjusted.active_handlers = merged;
            adjusted
        })
        .collect()
}

/// Return frames stored in a resumption are no longer owned by their
/// original live caller stack. Replaying `k` must consume the whole captured
/// chain; otherwise a frame restored from inside a library helper can stop at
/// its old `owner_initial_frame_count` and skip the user's post-loop code.
fn own_captured_return_frames(mut frames: Vec<CpsReturnFrame>) -> Vec<CpsReturnFrame> {
    for frame in &mut frames {
        frame.owner_initial_frame_count = 0;
    }
    frames
}

/// Pop and resume return frames innermost-first. Each frame's continuation
/// runs with its saved handler/guard state plus `extra_handlers` (handlers
/// installed in the calling eval AFTER the original Perform that created
/// the resumption — see `Resume` stmt for the typical case).
///
/// The Return terminator of each frame's eval will call this helper again
/// for the remaining frames, so this function only handles one step.
fn continue_return_frames(
    module: &CpsModule,
    value: CpsRuntimeValue,
    frames: &[CpsReturnFrame],
    extra_handlers: &[CpsHandlerFrame],
) -> CpsEvalResult<CpsRuntimeValue> {
    if frames.is_empty() {
        return Ok(value);
    }
    if matches!(value, CpsRuntimeValue::ScopeReturn { .. })
        || matches!(value, CpsRuntimeValue::Aborted(_))
        || matches!(value, CpsRuntimeValue::RoutedJump(_))
    {
        // A ScopeReturn from the inner eval should not have additional
        // frame continuations applied — propagate it untouched so the
        // caller's `dispatch_scope_return` can match the right prompt.
        return Ok(value);
    }
    let (frame, rest) = frames.split_last().expect("non-empty");
    trace_cps(
        "ContinueReturnFrames",
        format!(
            "pop owner={} cont={:?} owner_eval={} rest.len={} owner_initial={}",
            frame.owner_function,
            frame.continuation,
            frame.owner_eval_id.0,
            rest.len(),
            frame.owner_initial_frame_count,
        ),
    );
    let function = function_by_name(module, &frame.owner_function)?;
    let mut combined = frame.active_handlers.clone();
    for extra in extra_handlers {
        if !combined.iter().any(|f| f.prompt == extra.prompt) {
            combined.push(extra.clone());
        }
    }
    // Use resume_continuation (no into_inherited) so the saved handlers'
    // non-inherited state is preserved — that's how a ScopeReturn destined
    // for the handler scope in (e.g.) once_dfs_int can still resolve when
    // we're running work's post-call cont here. Also restore owner_eval_id
    // as current_eval_id so the install scope identity is preserved
    // (write22): the saved handlers' install_eval_id matches the eval that
    // installed them, and that's exactly the eval we're resuming.
    // owner_initial_frame_count may exceed rest.len() if a ScopeReturn
    // truncated frames after this one was pushed. Clamp so the resumed
    // owner eval can still proceed.
    let owner_initial = frame.owner_initial_frame_count.min(rest.len());
    resume_continuation(
        module,
        function,
        frame.continuation,
        vec![value],
        frame.values.as_ref().clone(),
        combined,
        frame.guard_stack.clone(),
        rest.to_vec(),
        frame.active_blocked.clone(),
        owner_initial,
        frame.owner_eval_id,
    )
}

/// write25 Step 5: walk-based ScopeReturn routing.
///
/// When `handle_scope_return` returns Propagate, the dispatching eval's
/// LOCAL `return_frames` may still hold the install scope for the SR's
/// handler. Specifically, the resumption's adjusted captured chain
/// (after `merge_extras_into_frames`) lives in the Resume eval's local
/// `return_frames` — and the modified copies there can hold handler
/// frames whose `install_eval_id == frame.owner_eval_id`, i.e. the
/// install scope of the handler is exactly that captured frame's owner
/// eval.
///
/// Walk innermost-first across the whole return-frame snapshot. For each frame, check
/// whether its saved `active_handlers` has a handler matching
/// `(prompt, install_eval_id == frame.owner_eval_id)` AND
/// `escape_owner_function == frame.owner_function`. If found, restore
/// that frame's eval at `handler.escape` with the in-scope handlers
/// truncated below the matched handler (so siblings above it survive),
/// and return the routed result.
///
/// Returns `None` when:
/// - the value is not a ScopeReturn,
/// - the target is `EXIT_RWH_TARGET` (RWH-escape — keep using
///   call-stack propagation for now),
/// - no own frame holds the install scope.
fn try_route_scope_return_through_return_frames(
    module: &CpsModule,
    scope_return: &CpsRuntimeValue,
    return_frames: &[CpsReturnFrame],
    initial_frame_count: usize,
) -> CpsEvalResult<Option<CpsRuntimeValue>> {
    let CpsRuntimeValue::ScopeReturn {
        prompt,
        target,
        value,
    } = scope_return
    else {
        return Ok(None);
    };
    let prompt = *prompt;
    let target = *target;
    if target == EXIT_RWH_TARGET {
        // write25 explicitly defers EXIT_RWH_TARGET routing through the
        // own-frame walk; existing RWH paths (which use the same sentinel
        // target) rely on call-stack propagation.
        return Ok(None);
    }
    if return_frames.is_empty() {
        return Ok(None);
    }
    trace_cps(
        "ScopeReturnFrameWalk",
        format!(
            "prompt={} target={:?} frames.len={} initial={}",
            prompt.0,
            target,
            return_frames.len(),
            initial_frame_count,
        ),
    );
    for frame_index in (0..return_frames.len()).rev() {
        let frame = &return_frames[frame_index];
        let frame_eval_id = frame.owner_eval_id;
        let frame_owner = &frame.owner_function;
        if trace_enabled() {
            trace_cps(
                "ScopeReturnFrameWalk",
                format!(
                    "  check frame_index={} owner={} owner_eval={} handlers={}",
                    frame_index,
                    frame.owner_function,
                    frame.owner_eval_id.0,
                    summarize_handler_stack(&frame.active_handlers),
                ),
            );
        }
        // Search this frame's snapshot for a handler that was installed
        // in this very frame's owner eval.
        let Some(handler_index) = frame.active_handlers.iter().rposition(|handler| {
            handler.prompt == prompt && handler.install_eval_id == frame_eval_id
        }) else {
            continue;
        };
        let matched_handler = frame.active_handlers[handler_index].clone();
        // owner check: the matched handler's escape must live in the
        // frame's owner function (so we can jump to it within that
        // eval). For non-EXIT targets this is required.
        if matched_handler.escape_owner_function != *frame_owner {
            continue;
        }
        debug_assert_eq!(
            matched_handler.install_eval_id, frame.owner_eval_id,
            "matched handler's install eval must equal frame.owner_eval_id"
        );
        // Build the post-jump handler stack: everything below the matched
        // handler stays in scope. Handlers above it (resume-site siblings
        // injected via `merge_extras_into_frames` between the anchor and
        // the captured inner tail) — write25 says truncate at the matched
        // index so they survive.
        // NOTE: For our anchor-based merge, the merged stack reads
        // `[outer, inner, H_sub]` with the matched H_sub at the end, so
        // truncating at `handler_index` keeps `[outer, inner]`. That's
        // exactly what we want.
        let mut post_handlers = frame.active_handlers.clone();
        post_handlers.truncate(handler_index);
        // Compute the rest of the frame chain. The matched frame is
        // consumed (we're jumping to its handler's escape). Frames after
        // it were already popped during the walk. Frames before it stay
        // as the resumed eval's inherited chain, but truncated to the
        // handler's install threshold (anything pushed in the handler's
        // scope is discarded).
        let mut rest_frames: Vec<CpsReturnFrame> = return_frames[..frame_index].to_vec();
        let threshold = matched_handler.return_frame_threshold;
        let rest_before = rest_frames.len();
        if rest_frames.len() > threshold {
            rest_frames.truncate(threshold);
        }
        let rest_after = rest_frames.len();
        trace_cps(
            "FrameWalkMatch",
            format!(
                "frame_owner={} frame_owner_eval={} handler_prompt={} handler_install_eval={} handlers_before={} handlers_after={} rest_before={} threshold={} rest_after={}",
                frame.owner_function,
                frame.owner_eval_id.0,
                matched_handler.prompt.0,
                matched_handler.install_eval_id.0,
                summarize_handler_stack(&frame.active_handlers),
                summarize_handler_stack(&post_handlers),
                rest_before,
                threshold,
                rest_after,
            ),
        );
        let owner_initial = frame.owner_initial_frame_count.min(rest_frames.len());
        if frame_index < initial_frame_count && post_handlers.is_empty() {
            return Ok(Some(CpsRuntimeValue::RoutedJump(Box::new(CpsRoutedJump {
                value: value.clone(),
                return_frame_threshold: threshold,
                owner_function: frame.owner_function.clone(),
                target: matched_handler.escape,
                values: frame.values.clone(),
                active_handlers: post_handlers,
                guard_stack: frame.guard_stack.clone(),
                return_frames: rest_frames,
                active_blocked: frame.active_blocked.clone(),
                initial_frame_count: owner_initial,
                eval_id: frame.owner_eval_id,
            }))));
        }
        let owner = function_by_name(module, &frame.owner_function)?;
        let result = resume_continuation(
            module,
            owner,
            matched_handler.escape,
            vec![*value.clone()],
            frame.values.as_ref().clone(),
            post_handlers,
            frame.guard_stack.clone(),
            rest_frames,
            frame.active_blocked.clone(),
            owner_initial,
            frame.owner_eval_id,
        )?;
        return Ok(Some(result));
    }
    Ok(None)
}

fn resolve_routed_jump(
    module: &CpsModule,
    value: CpsRuntimeValue,
    current_return_frames: &[CpsReturnFrame],
) -> CpsEvalResult<CpsRuntimeValue> {
    let CpsRuntimeValue::RoutedJump(jump) = value else {
        return Ok(value);
    };
    if current_return_frames.len() > jump.return_frame_threshold {
        return Ok(CpsRuntimeValue::RoutedJump(jump));
    }
    let owner = function_by_name(module, &jump.owner_function)?;
    resume_continuation(
        module,
        owner,
        jump.target,
        vec![*jump.value],
        jump.values.as_ref().clone(),
        jump.active_handlers,
        jump.guard_stack,
        jump.return_frames,
        jump.active_blocked,
        jump.initial_frame_count,
        jump.eval_id,
    )
}

fn function_by_name<'a>(module: &'a CpsModule, name: &str) -> CpsEvalResult<&'a CpsFunction> {
    module
        .functions
        .iter()
        .chain(module.roots.iter())
        .find(|function| function.name == name)
        .ok_or_else(|| CpsEvalError::MissingFunction {
            name: name.to_string(),
        })
}

fn continuation_by_id(
    function: &CpsFunction,
    id: CpsContinuationId,
) -> CpsEvalResult<&CpsContinuation> {
    function
        .continuations
        .iter()
        .find(|continuation| continuation.id == id)
        .ok_or_else(|| CpsEvalError::MissingContinuation {
            function: function.name.clone(),
            id,
        })
}

fn handler_arm_continues_to_installed_escape(
    function: &CpsFunction,
    handler: CpsHandlerId,
    entry: CpsContinuationId,
    escape: CpsContinuationId,
) -> bool {
    let escape_is_installed_for_handler = function.continuations.iter().any(|continuation| {
        continuation.stmts.iter().any(|stmt| {
            matches!(
                stmt,
                CpsStmt::InstallHandler {
                    handler: id,
                    escape: installed_escape,
                    ..
                } if *id == handler && *installed_escape == escape
            )
        })
    });
    if !escape_is_installed_for_handler {
        return false;
    }
    handler_arm_continue_chain_reaches_escape(function, handler, entry, escape)
}

fn handler_arm_continue_chain_reaches_escape(
    function: &CpsFunction,
    handler: CpsHandlerId,
    entry: CpsContinuationId,
    escape: CpsContinuationId,
) -> bool {
    let mut current = entry;
    let mut saw_uninstall = false;
    let mut visited = HashSet::new();
    while visited.insert(current) {
        let Some(continuation) = function
            .continuations
            .iter()
            .find(|continuation| continuation.id == current)
        else {
            return false;
        };
        saw_uninstall |= continuation.stmts.iter().any(
            |stmt| matches!(stmt, CpsStmt::UninstallHandler { handler: id } if *id == handler),
        );
        let CpsTerminator::Continue { target, .. } = &continuation.terminator else {
            return saw_uninstall && current == escape;
        };
        if *target == escape {
            return saw_uninstall;
        }
        current = *target;
    }
    false
}

fn handler_arm_uses_resume_with_handler(
    function: &CpsFunction,
    handler: CpsHandlerId,
    entry: CpsContinuationId,
) -> bool {
    let mut current = entry;
    let mut visited = HashSet::new();
    while visited.insert(current) {
        let Some(continuation) = function
            .continuations
            .iter()
            .find(|continuation| continuation.id == current)
        else {
            return false;
        };
        if continuation.stmts.iter().any(
            |stmt| matches!(stmt, CpsStmt::ResumeWithHandler { handler: id, .. } if *id == handler),
        ) {
            return true;
        }
        let CpsTerminator::Continue { target, .. } = &continuation.terminator else {
            return false;
        };
        current = *target;
    }
    false
}

fn handler_arm_for_stack<'a>(
    module: &'a CpsModule,
    current_function: &'a CpsFunction,
    stack: &'a [CpsHandlerFrame],
    effect: &typed_ir::Path,
    blocked: Option<u64>,
) -> CpsEvalResult<(
    &'a CpsHandlerArm,
    &'a CpsHandlerFrame,
    Vec<CpsHandlerFrame>,
    &'a CpsFunction,
)> {
    for (index, frame) in stack.iter().enumerate().rev() {
        if let Some(blocked) = blocked
            && frame.guard_stack.iter().any(|entry| entry.id == blocked)
        {
            trace_cps(
                "PerformHandlerSkip",
                format!(
                    "fn={} effect={:?} index={} prompt={} blocked={}",
                    current_function.name, effect, index, frame.prompt.0, blocked
                ),
            );
            continue;
        }
        for owner in module.functions.iter().chain(module.roots.iter()) {
            if let Some(arm) = owner
                .handlers
                .iter()
                .find(|handler| handler.id == frame.handler)
                .and_then(|handler| {
                    handler
                        .arms
                        .iter()
                        .find(|arm| effect_matches(&arm.effect, effect))
                })
            {
                return Ok((arm, frame, stack[..index].to_vec(), owner));
            }
        }
    }
    Err(CpsEvalError::MissingHandler {
        function: current_function.name.clone(),
        id: stack.last().expect("handler stack is non-empty").handler,
    })
}

fn handler_stack_with_static(
    active_handlers: &[CpsHandlerFrame],
    fallback: CpsHandlerId,
    guard_stack: &[CpsGuardEntry],
) -> Vec<CpsHandlerFrame> {
    if active_handlers.is_empty() {
        // Synthetic frame for the static-fallback path. Real escape target
        // is unknown at this point, so we use EXIT_RWH_TARGET so an abort
        // at this synthetic frame surfaces back through the call boundary.
        // install_eval_id = SYNTHETIC_EVAL_ID: this frame must never act
        // as a ScopeReturn resolver — the perform's arm body, not a
        // matching install scope, decides the value here.
        vec![CpsHandlerFrame {
            prompt: fresh_prompt(),
            handler: fallback,
            guard_stack: guard_stack.to_vec(),
            envs: Vec::new(),
            escape: EXIT_RWH_TARGET,
            escape_owner_function: String::new(),
            inherited: false,
            return_frame_threshold: 0,
            install_eval_id: SYNTHETIC_EVAL_ID,
        }]
    } else {
        active_handlers.to_vec()
    }
}

#[allow(dead_code)]
fn handler_stack_with_pushed(
    active_handlers: &[CpsHandlerFrame],
    handler: CpsHandlerId,
    guard_stack: &[CpsGuardEntry],
    envs: Vec<CpsEvaluatedHandlerEnv>,
) -> Vec<CpsHandlerFrame> {
    let mut stack = active_handlers.to_vec();
    stack.push(CpsHandlerFrame {
        prompt: fresh_prompt(),
        handler,
        guard_stack: guard_stack.to_vec(),
        envs,
        // ResumeWithHandler-installed frame: arm result returns to the
        // outer eval frame (the call site that ran this stmt).
        escape: EXIT_RWH_TARGET,
        escape_owner_function: String::new(),
        inherited: false,
        return_frame_threshold: 0,
        // Dead code currently — but if revived, the caller must pass a
        // real eval id. SYNTHETIC keeps it safe.
        install_eval_id: SYNTHETIC_EVAL_ID,
    });
    stack
}

fn capture_handler_envs(
    function: &CpsFunction,
    values: &[Option<CpsRuntimeValue>],
    envs: &[CpsHandlerEnv],
) -> CpsEvalResult<Vec<CpsEvaluatedHandlerEnv>> {
    envs.iter()
        .map(|env| {
            let mut values_by_id = Vec::new();
            for (index, value) in env.values.iter().enumerate() {
                let target = env.targets.get(index).copied().unwrap_or(*value);
                values_by_id.push((target, read_value(function, values, *value)?));
            }
            Ok(CpsEvaluatedHandlerEnv {
                entry: env.entry,
                values: values_by_id,
            })
        })
        .collect()
}

fn overlay_handler_envs_in_frames(
    function: &str,
    frames: &mut [CpsReturnFrame],
    handler: CpsHandlerId,
    updates: &[CpsEvaluatedHandlerEnv],
    remember_latest: bool,
) {
    for frame in frames {
        overlay_handler_envs_in_stack(
            function,
            &mut frame.active_handlers,
            handler,
            updates,
            remember_latest,
        );
    }
}

fn overlay_handler_envs_in_stack(
    function: &str,
    stack: &mut [CpsHandlerFrame],
    handler: CpsHandlerId,
    updates: &[CpsEvaluatedHandlerEnv],
    remember_latest: bool,
) {
    if updates.is_empty() {
        return;
    }
    for frame in stack.iter_mut().filter(|frame| frame.handler == handler) {
        overlay_handler_envs(&mut frame.envs, updates);
    }
    if remember_latest {
        remember_latest_handler_envs(handler, updates);
    }
    push_cps_frame_trace_event(CpsFrameTraceEvent::HandlerEnvOverlay {
        layer: CpsFrameTraceLayer::CpsEval,
        function: function.to_string(),
        handler: handler.0,
        entries: updates.iter().map(|env| env.entry.0).collect(),
        values: trace_cps_handler_env_slots(updates),
    });
}

fn overlay_handler_envs(
    envs: &mut Vec<CpsEvaluatedHandlerEnv>,
    updates: &[CpsEvaluatedHandlerEnv],
) {
    for update in updates {
        let Some(existing) = envs.iter_mut().find(|env| env.entry == update.entry) else {
            envs.push(update.clone());
            continue;
        };
        for (target, value) in &update.values {
            if let Some((_, existing_value)) = existing
                .values
                .iter_mut()
                .find(|(existing_target, _)| existing_target == target)
            {
                *existing_value = value.clone();
            } else {
                existing.values.push((*target, value.clone()));
            }
        }
    }
}

fn remember_latest_handler_envs(handler: CpsHandlerId, updates: &[CpsEvaluatedHandlerEnv]) {
    LATEST_HANDLER_ENVS.with(|latest| {
        let mut latest = latest.borrow_mut();
        for update in updates {
            for (target, value) in &update.values {
                if let Some(existing) = latest.iter_mut().find(|existing| {
                    existing.handler == handler
                        && existing.entry == update.entry
                        && existing.target == *target
                }) {
                    existing.value = value.clone();
                } else {
                    latest.push(CpsLatestHandlerEnv {
                        handler,
                        entry: update.entry,
                        target: *target,
                        value: value.clone(),
                    });
                }
            }
        }
    });
}

fn latest_handler_env_value(
    handler: CpsHandlerId,
    entry: CpsContinuationId,
    target: CpsValueId,
) -> Option<CpsRuntimeValue> {
    LATEST_HANDLER_ENVS.with(|latest| {
        latest
            .borrow()
            .iter()
            .rev()
            .find(|latest| {
                latest.handler == handler && latest.entry == entry && latest.target == target
            })
            .map(|latest| latest.value.clone())
    })
}

fn values_with_handler_env(
    function: &str,
    mut values: Vec<Option<CpsRuntimeValue>>,
    frame: &CpsHandlerFrame,
    entry: CpsContinuationId,
) -> Vec<Option<CpsRuntimeValue>> {
    let Some(env) = frame.envs.iter().find(|env| env.entry == entry) else {
        return values;
    };
    let effective_values = env
        .values
        .iter()
        .map(|(id, value)| {
            (
                *id,
                latest_handler_env_value(frame.handler, entry, *id)
                    .unwrap_or_else(|| value.clone()),
            )
        })
        .collect::<Vec<_>>();
    push_cps_frame_trace_event(CpsFrameTraceEvent::HandlerEnvRead {
        layer: CpsFrameTraceLayer::CpsEval,
        function: function.to_string(),
        handler: frame.handler.0,
        entry: entry.0,
        values: trace_cps_handler_env_value_slots(&effective_values),
    });
    for (id, value) in effective_values {
        write_value(&mut values, id, value);
    }
    values
}

fn trace_cps_handler_env_slots(envs: &[CpsEvaluatedHandlerEnv]) -> Vec<CpsFrameTraceSlot> {
    envs.iter()
        .flat_map(|env| {
            env.values.iter().map(|(target, value)| CpsFrameTraceSlot {
                target: target.0,
                value: summarize_cps_value(value),
            })
        })
        .collect()
}

fn trace_cps_handler_env_value_slots(
    values: &[(CpsValueId, CpsRuntimeValue)],
) -> Vec<CpsFrameTraceSlot> {
    values
        .iter()
        .map(|(target, value)| CpsFrameTraceSlot {
            target: target.0,
            value: summarize_cps_value(value),
        })
        .collect()
}

fn add_thunk_boundary(
    value: CpsRuntimeValue,
    guard_id: u64,
    allowed: typed_ir::Type,
    active: bool,
) -> CpsRuntimeValue {
    let CpsRuntimeValue::Thunk(thunk) = value else {
        return value;
    };
    let mut blocked = thunk.blocked.as_ref().clone();
    blocked.push(CpsBlockedEffect {
        guard_id,
        allowed,
        active,
    });
    CpsRuntimeValue::Thunk(Rc::new(CpsThunk {
        owner_function: thunk.owner_function.clone(),
        entry: thunk.entry,
        values: thunk.values.clone(),
        handlers: thunk.handlers.clone(),
        guard_stack: thunk.guard_stack.clone(),
        blocked: Rc::new(blocked),
    }))
}

fn active_blocked_for_thunk(
    current: &[CpsBlockedEffect],
    thunk: &CpsThunk,
) -> Vec<CpsBlockedEffect> {
    let mut active = current.to_vec();
    active.extend(
        thunk
            .blocked
            .iter()
            .filter(|blocked| blocked.active)
            .cloned(),
    );
    active
}

fn active_blocked_id(effect: &typed_ir::Path, active: &[CpsBlockedEffect]) -> Option<u64> {
    active
        .iter()
        .rev()
        .find(|blocked| !effect_allowed_by_type(&blocked.allowed, effect))
        .map(|blocked| blocked.guard_id)
}

fn effect_allowed_by_type(allowed: &typed_ir::Type, effect: &typed_ir::Path) -> bool {
    match allowed {
        typed_ir::Type::Any => true,
        typed_ir::Type::Never => false,
        typed_ir::Type::Named { path, .. } => effect_path_matches_allowed(path, effect),
        typed_ir::Type::Row { items, tail } => {
            items
                .iter()
                .any(|item| effect_allowed_by_type(item, effect))
                || matches!(tail.as_ref(), typed_ir::Type::Any)
        }
        _ => false,
    }
}

fn effect_path_matches_allowed(allowed: &typed_ir::Path, effect: &typed_ir::Path) -> bool {
    if effect.segments.starts_with(&allowed.segments) {
        return true;
    }
    if allowed.segments.len() > 1
        && effect.segments.len() == allowed.segments.len()
        && effect.segments[..effect.segments.len() - 1]
            == allowed.segments[..allowed.segments.len() - 1]
        && effect_segment_matches_allowed(
            &allowed.segments[allowed.segments.len() - 1],
            &effect.segments[effect.segments.len() - 1],
        )
    {
        return true;
    }
    effect
        .segments
        .iter()
        .enumerate()
        .skip(1)
        .any(|(index, _)| effect.segments[index..].starts_with(&allowed.segments))
}

fn effect_segment_matches_allowed(allowed: &typed_ir::Name, effect: &typed_ir::Name) -> bool {
    allowed == effect
        || effect
            .0
            .strip_suffix("#effect")
            .is_some_and(|base| base == allowed.0)
}

fn effect_matches(expected: &typed_ir::Path, actual: &typed_ir::Path) -> bool {
    effect_path_matches_allowed(expected, actual)
}

fn assign_continuation_args(
    values: &mut Vec<Option<CpsRuntimeValue>>,
    function: &CpsFunction,
    continuation: &CpsContinuation,
    args: Vec<CpsRuntimeValue>,
) -> CpsEvalResult<()> {
    if continuation.params.len() != args.len() {
        return Err(CpsEvalError::ContinuationArgumentMismatch {
            function: function.name.clone(),
            id: continuation.id,
            expected: continuation.params.len(),
            actual: args.len(),
        });
    }
    for (param, value) in continuation.params.iter().copied().zip(args) {
        write_value(values, param, value);
    }
    Ok(())
}

fn write_value(values: &mut Vec<Option<CpsRuntimeValue>>, id: CpsValueId, value: CpsRuntimeValue) {
    if values.len() <= id.0 {
        values.resize_with(id.0 + 1, || None);
    }
    values[id.0] = Some(value);
}

fn read_value(
    function: &CpsFunction,
    values: &[Option<CpsRuntimeValue>],
    id: CpsValueId,
) -> CpsEvalResult<CpsRuntimeValue> {
    values
        .get(id.0)
        .and_then(Clone::clone)
        .ok_or_else(|| CpsEvalError::MissingValue {
            function: function.name.clone(),
            id,
        })
}

fn read_plain_value(
    function: &CpsFunction,
    values: &[Option<CpsRuntimeValue>],
    id: CpsValueId,
) -> CpsEvalResult<runtime::VmValue> {
    into_plain_value(function, id, read_value(function, values, id)?)
}

fn read_effect_id(
    function: &CpsFunction,
    values: &[Option<CpsRuntimeValue>],
    id: CpsValueId,
) -> CpsEvalResult<u64> {
    match read_plain_value(function, values, id)? {
        runtime::VmValue::EffectId(value_id) => Ok(value_id),
        value => Err(CpsEvalError::ExpectedGuard {
            function: function.name.clone(),
            id,
            value,
        }),
    }
}

fn into_plain_value(
    function: &CpsFunction,
    id: CpsValueId,
    value: CpsRuntimeValue,
) -> CpsEvalResult<runtime::VmValue> {
    cps_value_to_vm(value).ok_or_else(|| CpsEvalError::ExpectedPlainValue {
        function: function.name.clone(),
        id,
    })
}

fn read_resumption(
    function: &CpsFunction,
    values: &[Option<CpsRuntimeValue>],
    id: CpsValueId,
) -> CpsEvalResult<Rc<CpsResumption>> {
    match read_value(function, values, id)? {
        CpsRuntimeValue::Resumption(resumption) => Ok(resumption),
        _ => Err(CpsEvalError::ExpectedResumption {
            function: function.name.clone(),
            id,
        }),
    }
}

#[allow(dead_code)]
fn read_closure(
    function: &CpsFunction,
    values: &[Option<CpsRuntimeValue>],
    id: CpsValueId,
) -> CpsEvalResult<Rc<CpsClosure>> {
    match read_value(function, values, id)? {
        CpsRuntimeValue::Closure(closure) => Ok(closure),
        _ => Err(CpsEvalError::ExpectedPlainValue {
            function: function.name.clone(),
            id,
        }),
    }
}

#[derive(Debug, Clone, PartialEq)]
enum CpsRuntimeValue {
    Plain(runtime::VmValue),
    Resumption(Rc<CpsResumption>),
    Thunk(Rc<CpsThunk>),
    Closure(Rc<CpsClosure>),
    /// First-class CPS containers whose elements may themselves be
    /// resumptions, thunks, closures, or other CPS values. Used by
    /// `std::undet.once`'s `list<resumption>` queue and `(k, queue)` tuple
    /// pattern, which a `VmValue::List`/`Tuple` cannot represent.
    List(Rc<Vec<CpsRuntimeValue>>),
    Tuple(Vec<CpsRuntimeValue>),
    Record(BTreeMap<typed_ir::Name, CpsRuntimeValue>),
    Variant {
        tag: typed_ir::Name,
        value: Option<Box<CpsRuntimeValue>>,
    },
    /// A frame-walk ScopeReturn resolved to a handler escape owned by an
    /// outer live eval frame. Carry the jump until that eval frontier is
    /// reached, then execute the escape as ordinary value flow.
    RoutedJump(Box<CpsRoutedJump>),
    /// A routed non-local result that must keep bubbling through live host
    /// calls without executing their remaining continuation code.
    #[allow(dead_code)]
    Aborted(Box<CpsRuntimeValue>),
    /// Non-local return carrying a value to a specific handler-installed scope.
    /// Generated when a `Perform`'s arm body completes; propagates through call
    /// sites until the matching prompt is found in `active_handlers`. A frame
    /// matches by `prompt` (a dynamic id, fresh per `InstallHandler` /
    /// `ResumeWithHandler` execution), so recursive handler scopes don't get
    /// confused with each other. When matched, the prompt's owning frame and
    /// any inner frames are popped, and:
    ///   - if `target != EXIT_RWH_TARGET`, control jumps to that continuation
    ///     with `value` as its single argument;
    ///   - if `target == EXIT_RWH_TARGET`, the eval frame returns `value` as
    ///     its result so the matching `ResumeWithHandler` call site sees a
    ///     plain return.
    ScopeReturn {
        prompt: CpsPromptId,
        target: CpsContinuationId,
        value: Box<CpsRuntimeValue>,
    },
}

#[derive(Debug, Clone, PartialEq)]
struct CpsRoutedJump {
    value: Box<CpsRuntimeValue>,
    return_frame_threshold: usize,
    owner_function: String,
    target: CpsContinuationId,
    values: Rc<Vec<Option<CpsRuntimeValue>>>,
    active_handlers: Vec<CpsHandlerFrame>,
    guard_stack: Vec<CpsGuardEntry>,
    return_frames: Vec<CpsReturnFrame>,
    active_blocked: Vec<CpsBlockedEffect>,
    initial_frame_count: usize,
    eval_id: CpsEvalId,
}

/// Sentinel `target` value used by `ResumeWithHandler`-installed handler
/// frames to mean "no continuation target — just return the value to the
/// outer eval frame." Picked as `usize::MAX` since real continuation ids
/// are dense small integers.
const EXIT_RWH_TARGET: CpsContinuationId = CpsContinuationId(usize::MAX);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
struct CpsPromptId(u64);

thread_local! {
    static PROMPT_COUNTER: std::cell::Cell<u64> = const { std::cell::Cell::new(0) };
}

fn fresh_prompt() -> CpsPromptId {
    PROMPT_COUNTER.with(|cell| {
        let id = cell.get();
        cell.set(id + 1);
        CpsPromptId(id)
    })
}

/// Identity of an eval frame instance. Distinct from function name and
/// continuation id: a recursive resumption can run the same function in a
/// fresh eval frame, and we must not let a ScopeReturn from the fresh
/// frame resolve a handler installed by the original frame. See write22.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
struct CpsEvalId(u64);

thread_local! {
    static EVAL_ID_COUNTER: std::cell::Cell<u64> = const { std::cell::Cell::new(0) };
}

fn fresh_eval_id() -> CpsEvalId {
    EVAL_ID_COUNTER.with(|cell| {
        let id = cell.get();
        cell.set(id + 1);
        CpsEvalId(id)
    })
}

/// Sentinel eval id used for synthetic handler frames (Perform fallback
/// without an installed handler) that should never participate in
/// ScopeReturn resolution. Picking a fresh id at synth time would work
/// too, but using a sentinel makes traces clearer.
const SYNTHETIC_EVAL_ID: CpsEvalId = CpsEvalId(u64::MAX);

/// Identifier of the handler frame whose arm produced a resumption. Used
/// to anchor handler-stack merging at Resume time: the resume-site's
/// sibling handlers (installed in the arm body, e.g. `loop`'s inner
/// recursive handler in `std::undet::once`) belong immediately AFTER
/// this anchor in the merged stack so they sit between the captured
/// outer handlers and the captured inner tail (write24 Step 1).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct CpsHandlerAnchor {
    prompt: CpsPromptId,
    install_eval_id: CpsEvalId,
}

#[derive(Debug, Clone, PartialEq)]
struct CpsResumption {
    owner_function: String,
    target: CpsContinuationId,
    values: Rc<Vec<Option<CpsRuntimeValue>>>,
    handlers: Rc<Vec<CpsHandlerFrame>>,
    guard_stack: Rc<Vec<CpsGuardEntry>>,
    active_blocked: Rc<Vec<CpsBlockedEffect>>,
    /// Stack of return frames representing caller continuations that were
    /// suspended waiting for this resumption. When the resumption is resumed,
    /// its local continuation runs first; if it returns normally the frames
    /// are continued in order (innermost first).
    return_frames: Rc<Vec<CpsReturnFrame>>,
    /// The handler frame whose arm body created this resumption. `None`
    /// when the perform fell through to a synthetic static-fallback frame
    /// (no installed handler in active_handlers at perform time). Used by
    /// `merge_resumption_handlers` to place resume-site siblings at the
    /// correct stack depth.
    handled_anchor: Option<CpsHandlerAnchor>,
}

struct CapturedPromptContinuation {
    handlers: Vec<CpsHandlerFrame>,
    return_frames: Vec<CpsReturnFrame>,
}

/// A suspended caller continuation. Pushed by effectful terminators
/// (EffectfulCall / EffectfulApply / EffectfulForce) when a potentially-
/// effectful call is made inside a handler scope. Stored in
/// `CpsResumption.return_frames` so that resuming k also resumes the
/// caller's computation after the call.
#[derive(Debug, Clone, PartialEq)]
struct CpsReturnFrame {
    prompt_exit: Option<CpsPromptExitFrame>,
    owner_function: String,
    continuation: CpsContinuationId,
    values: Rc<Vec<Option<CpsRuntimeValue>>>,
    /// Handler snapshot at the effectful-call site, BEFORE the callee's
    /// `into_inherited` pass. Restored as-is (non-inherited frames remain
    /// non-inherited) when the frame is re-entered via `continue_return_frames`.
    active_handlers: Vec<CpsHandlerFrame>,
    guard_stack: Vec<CpsGuardEntry>,
    active_blocked: Vec<CpsBlockedEffect>,
    /// Threshold for the owner eval's `initial_frame_count` — i.e. how
    /// many of *its* return_frames were inherited from above when this
    /// frame was pushed. Restored when the owner is re-entered via
    /// `continue_return_frames` so the owner's Return only consumes its
    /// own pushed frames, not the ones it inherited.
    owner_initial_frame_count: usize,
    /// Identity of the eval frame that pushed this return frame. When
    /// `continue_return_frames` resumes the owner continuation, this id is
    /// restored as `current_eval_id` so `ScopeReturn` resolution targets
    /// the same eval frame that originally installed the matching handler
    /// (write22).
    owner_eval_id: CpsEvalId,
}

#[derive(Debug, Clone, PartialEq)]
struct CpsPromptExitFrame {
    prompt: CpsPromptId,
}

#[derive(Debug, Clone, PartialEq)]
struct CpsThunk {
    owner_function: String,
    entry: CpsContinuationId,
    values: Rc<Vec<Option<CpsRuntimeValue>>>,
    handlers: Rc<Vec<CpsHandlerFrame>>,
    guard_stack: Rc<Vec<CpsGuardEntry>>,
    blocked: Rc<Vec<CpsBlockedEffect>>,
}

#[derive(Debug, Clone, PartialEq)]
struct CpsBlockedEffect {
    guard_id: u64,
    allowed: typed_ir::Type,
    active: bool,
}

#[derive(Debug, Clone, PartialEq)]
struct CpsClosure {
    owner_function: String,
    entry: CpsContinuationId,
    values: Rc<Vec<Option<CpsRuntimeValue>>>,
    recursive_self: Option<CpsValueId>,
}

#[derive(Debug, Clone, PartialEq)]
struct CpsHandlerFrame {
    /// Dynamic prompt id, fresh per scope install. Matched by `ScopeReturn`
    /// so recursive handler installs (e.g. `std::undet.once`'s `loop`) don't
    /// alias each other on the way up.
    prompt: CpsPromptId,
    handler: CpsHandlerId,
    guard_stack: Vec<CpsGuardEntry>,
    envs: Vec<CpsEvaluatedHandlerEnv>,
    /// Continuation in `escape_owner_function` reached when the handler scope
    /// completes. Set to `EXIT_RWH_TARGET` for frames pushed by
    /// `ResumeWithHandler` — they bottom out at the call site.
    escape: CpsContinuationId,
    /// Name of the function whose CPS body holds the `escape` continuation.
    /// `ScopeReturn` only resolves into a jump in that function's eval frame;
    /// elsewhere it must propagate up.
    escape_owner_function: String,
    /// `return_frames.len()` at the time this handler was installed. When a
    /// `ScopeReturn` jumps via this handler's escape, return_frames pushed
    /// after install are inside the handler's scope and must be discarded
    /// (delimited continuation semantics: non-local exit cuts the slice
    /// inside the handler). Without this, an early `sub::return` would
    /// still trigger trailing reject() in the saved frames.
    return_frame_threshold: usize,
    /// True iff this frame is part of a resumption snapshot (i.e. the
    /// `resumption.handlers` of a `Resume` / `ResumeWithHandler`). Kept as
    /// auxiliary info — `Perform`-time handler search still uses it. The
    /// primary check for `ScopeReturn` resolution is `install_eval_id`
    /// below, which is more precise.
    inherited: bool,
    /// Identity of the eval frame that ran `InstallHandler` to create this
    /// frame. A `ScopeReturn` only resolves at a handler whose
    /// `install_eval_id == current_eval_id`. Function identity is not
    /// enough: a multi-shot resumption can run the same CPS function in a
    /// fresh eval frame, and that fresh frame must not catch a handler
    /// installed by the original eval (write22).
    install_eval_id: CpsEvalId,
}

#[derive(Debug, Clone, PartialEq)]
struct CpsEvaluatedHandlerEnv {
    entry: CpsContinuationId,
    values: Vec<(CpsValueId, CpsRuntimeValue)>,
}

#[derive(Debug, Clone, PartialEq)]
struct CpsLatestHandlerEnv {
    handler: CpsHandlerId,
    entry: CpsContinuationId,
    target: CpsValueId,
    value: CpsRuntimeValue,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct CpsGuardEntry {
    var: runtime::EffectIdVar,
    id: u64,
}

fn eval_literal(lit: &CpsLiteral) -> runtime::VmValue {
    match lit {
        CpsLiteral::Int(value) => runtime::VmValue::Int(value.clone()),
        CpsLiteral::Float(value) => runtime::VmValue::Float(value.clone()),
        CpsLiteral::String(value) => {
            runtime::VmValue::String(runtime::runtime::string_tree::StringTree::from_str(value))
        }
        CpsLiteral::Bool(value) => runtime::VmValue::Bool(*value),
        CpsLiteral::Unit => runtime::VmValue::Unit,
    }
}

/// Evaluate a primitive op over CPS runtime values. List ops can carry
/// resumptions / closures / thunks, so the list/append/uncons family stays
/// inside the CpsRuntimeValue domain. Everything else falls back to the VM
/// primitive after converting args and result through `cps_value_to_vm` /
/// `cps_value_from_vm`.
fn eval_cps_primitive(
    op: typed_ir::PrimitiveOp,
    args: Vec<CpsRuntimeValue>,
) -> CpsEvalResult<CpsRuntimeValue> {
    use typed_ir::PrimitiveOp;
    match op {
        PrimitiveOp::ListEmpty => {
            // ListEmpty's runtime arity is 1 (a unit witness). Accept and
            // ignore the argument so list<resumption> empties land in the
            // CPS value domain.
            if args.len() > 1 {
                return Err(CpsEvalError::InvalidPrimitiveArity {
                    op,
                    expected: 1,
                    actual: args.len(),
                });
            }
            Ok(CpsRuntimeValue::List(Rc::new(Vec::new())))
        }
        PrimitiveOp::ListSingleton => {
            if args.len() != 1 {
                return Err(CpsEvalError::InvalidPrimitiveArity {
                    op,
                    expected: 1,
                    actual: args.len(),
                });
            }
            Ok(CpsRuntimeValue::List(Rc::new(vec![
                args.into_iter().next().unwrap(),
            ])))
        }
        PrimitiveOp::ListMerge => {
            if args.len() != 2 {
                return Err(CpsEvalError::InvalidPrimitiveArity {
                    op,
                    expected: 2,
                    actual: args.len(),
                });
            }
            let mut iter = args.into_iter();
            let left = iter.next().unwrap();
            let right = iter.next().unwrap();
            let mut merged = control_list_items(op, left)?;
            merged.extend(control_list_items(op, right)?);
            Ok(CpsRuntimeValue::List(Rc::new(merged)))
        }
        PrimitiveOp::ListLen => {
            if args.len() != 1 {
                return Err(CpsEvalError::InvalidPrimitiveArity {
                    op,
                    expected: 1,
                    actual: args.len(),
                });
            }
            let items = control_list_items(op, args.into_iter().next().unwrap())?;
            Ok(CpsRuntimeValue::Plain(runtime::VmValue::Int(
                items.len().to_string(),
            )))
        }
        PrimitiveOp::ListIndex => {
            if args.len() != 2 {
                return Err(CpsEvalError::InvalidPrimitiveArity {
                    op,
                    expected: 2,
                    actual: args.len(),
                });
            }
            let mut iter = args.into_iter();
            let list = iter.next().unwrap();
            let idx_val = iter.next().unwrap();
            let items = control_list_items(op, list)?;
            let idx = cps_value_to_usize(op, idx_val)?;
            items
                .into_iter()
                .nth(idx)
                .ok_or(CpsEvalError::UnsupportedPrimitive { op })
        }
        PrimitiveOp::ListIndexRangeRaw => {
            if args.len() != 3 {
                return Err(CpsEvalError::InvalidPrimitiveArity {
                    op,
                    expected: 3,
                    actual: args.len(),
                });
            }
            let mut iter = args.into_iter();
            let list = iter.next().unwrap();
            let start_val = iter.next().unwrap();
            let end_val = iter.next().unwrap();
            let items = control_list_items(op, list)?;
            let start = cps_value_to_usize(op, start_val)?;
            let end = cps_value_to_usize(op, end_val)?;
            Ok(CpsRuntimeValue::List(Rc::new(
                items.into_iter().skip(start).take(end - start).collect(),
            )))
        }
        _ => {
            let plain_args = args
                .into_iter()
                .map(cps_value_to_vm)
                .collect::<Option<Vec<_>>>()
                .ok_or(CpsEvalError::UnsupportedPrimitive { op })?;
            eval_primitive(op, &plain_args).map(cps_value_from_vm)
        }
    }
}

fn cps_value_to_usize(op: typed_ir::PrimitiveOp, value: CpsRuntimeValue) -> CpsEvalResult<usize> {
    match value {
        CpsRuntimeValue::Plain(runtime::VmValue::Int(s)) => s
            .parse::<usize>()
            .map_err(|_| CpsEvalError::UnsupportedPrimitive { op }),
        _ => Err(CpsEvalError::UnsupportedPrimitive { op }),
    }
}

fn control_list_items(
    op: typed_ir::PrimitiveOp,
    value: CpsRuntimeValue,
) -> CpsEvalResult<Vec<CpsRuntimeValue>> {
    match value {
        CpsRuntimeValue::List(items) => Ok(items.as_ref().clone()),
        CpsRuntimeValue::Plain(plain) => match plain {
            runtime::VmValue::List(list) => Ok(list
                .to_vec()
                .into_iter()
                .map(|item| cps_value_from_vm((*item).clone()))
                .collect()),
            other => Err(CpsEvalError::PrimitiveTypeMismatch { op, value: other }),
        },
        _ => Err(CpsEvalError::UnsupportedPrimitive { op }),
    }
}

fn eval_primitive(
    op: typed_ir::PrimitiveOp,
    args: &[runtime::VmValue],
) -> CpsEvalResult<runtime::VmValue> {
    crate::eval::eval_primitive_for_abi(op, args).map_err(cps_eval_primitive_error)
}

fn bool_value(op: typed_ir::PrimitiveOp, value: &runtime::VmValue) -> CpsEvalResult<bool> {
    match value {
        runtime::VmValue::Bool(value) => Ok(*value),
        value => Err(CpsEvalError::PrimitiveTypeMismatch {
            op,
            value: value.clone(),
        }),
    }
}

fn cps_eval_primitive_error(error: crate::eval::NativeEvalError) -> CpsEvalError {
    match error {
        crate::eval::NativeEvalError::InvalidPrimitiveArity {
            op,
            expected,
            actual,
        } => CpsEvalError::InvalidPrimitiveArity {
            op,
            expected,
            actual,
        },
        crate::eval::NativeEvalError::PrimitiveTypeMismatch { op, value } => {
            CpsEvalError::PrimitiveTypeMismatch { op, value }
        }
        crate::eval::NativeEvalError::UnsupportedPrimitive { op } => {
            CpsEvalError::UnsupportedPrimitive { op }
        }
        other => unreachable!("native primitive evaluator returned non-primitive error: {other}"),
    }
}

#[cfg(test)]
mod tests {
    use std::rc::Rc;

    use crate::cps_ir::{
        CpsContinuation, CpsContinuationId, CpsFunction, CpsHandler, CpsHandlerArm, CpsHandlerId,
        CpsLiteral, CpsModule, CpsShotKind, CpsStmt, CpsTerminator, CpsValueId,
    };
    use crate::cps_validate::validate_cps_module;

    use super::*;

    #[test]
    fn evaluates_plain_value_primitives_through_native_evaluator() {
        let string_root = CpsFunction {
            name: "string-root".to_string(),
            params: Vec::new(),
            entry: CpsContinuationId(0),
            handlers: Vec::new(),
            continuations: vec![CpsContinuation {
                id: CpsContinuationId(0),
                params: Vec::new(),
                captures: Vec::new(),
                shot_kind: CpsShotKind::OneShot,
                stmts: vec![
                    CpsStmt::Literal {
                        dest: CpsValueId(0),
                        literal: CpsLiteral::String("aあ🙂z".to_string()),
                    },
                    CpsStmt::Literal {
                        dest: CpsValueId(1),
                        literal: CpsLiteral::Int("1".to_string()),
                    },
                    CpsStmt::Literal {
                        dest: CpsValueId(2),
                        literal: CpsLiteral::Int("3".to_string()),
                    },
                    CpsStmt::Literal {
                        dest: CpsValueId(3),
                        literal: CpsLiteral::String("bc".to_string()),
                    },
                    CpsStmt::Primitive {
                        dest: CpsValueId(4),
                        op: typed_ir::PrimitiveOp::StringSpliceRaw,
                        args: vec![CpsValueId(0), CpsValueId(1), CpsValueId(2), CpsValueId(3)],
                    },
                ],
                terminator: CpsTerminator::Return(CpsValueId(4)),
            }],
        };
        let list_root = CpsFunction {
            name: "list-root".to_string(),
            params: Vec::new(),
            entry: CpsContinuationId(0),
            handlers: Vec::new(),
            continuations: vec![CpsContinuation {
                id: CpsContinuationId(0),
                params: Vec::new(),
                captures: Vec::new(),
                shot_kind: CpsShotKind::OneShot,
                stmts: vec![
                    CpsStmt::Literal {
                        dest: CpsValueId(0),
                        literal: CpsLiteral::Int("1".to_string()),
                    },
                    CpsStmt::Literal {
                        dest: CpsValueId(1),
                        literal: CpsLiteral::Int("2".to_string()),
                    },
                    CpsStmt::Literal {
                        dest: CpsValueId(2),
                        literal: CpsLiteral::Int("3".to_string()),
                    },
                    CpsStmt::Literal {
                        dest: CpsValueId(3),
                        literal: CpsLiteral::Int("4".to_string()),
                    },
                    CpsStmt::Primitive {
                        dest: CpsValueId(4),
                        op: typed_ir::PrimitiveOp::ListSingleton,
                        args: vec![CpsValueId(0)],
                    },
                    CpsStmt::Primitive {
                        dest: CpsValueId(5),
                        op: typed_ir::PrimitiveOp::ListSingleton,
                        args: vec![CpsValueId(1)],
                    },
                    CpsStmt::Primitive {
                        dest: CpsValueId(6),
                        op: typed_ir::PrimitiveOp::ListMerge,
                        args: vec![CpsValueId(4), CpsValueId(5)],
                    },
                    CpsStmt::Primitive {
                        dest: CpsValueId(7),
                        op: typed_ir::PrimitiveOp::ListSingleton,
                        args: vec![CpsValueId(2)],
                    },
                    CpsStmt::Primitive {
                        dest: CpsValueId(8),
                        op: typed_ir::PrimitiveOp::ListMerge,
                        args: vec![CpsValueId(6), CpsValueId(7)],
                    },
                    CpsStmt::Primitive {
                        dest: CpsValueId(9),
                        op: typed_ir::PrimitiveOp::ListSingleton,
                        args: vec![CpsValueId(3)],
                    },
                    CpsStmt::Primitive {
                        dest: CpsValueId(10),
                        op: typed_ir::PrimitiveOp::ListMerge,
                        args: vec![CpsValueId(8), CpsValueId(9)],
                    },
                    CpsStmt::Literal {
                        dest: CpsValueId(11),
                        literal: CpsLiteral::Int("8".to_string()),
                    },
                    CpsStmt::Literal {
                        dest: CpsValueId(12),
                        literal: CpsLiteral::Int("9".to_string()),
                    },
                    CpsStmt::Primitive {
                        dest: CpsValueId(13),
                        op: typed_ir::PrimitiveOp::ListSingleton,
                        args: vec![CpsValueId(11)],
                    },
                    CpsStmt::Primitive {
                        dest: CpsValueId(14),
                        op: typed_ir::PrimitiveOp::ListSingleton,
                        args: vec![CpsValueId(12)],
                    },
                    CpsStmt::Primitive {
                        dest: CpsValueId(15),
                        op: typed_ir::PrimitiveOp::ListMerge,
                        args: vec![CpsValueId(13), CpsValueId(14)],
                    },
                    CpsStmt::Literal {
                        dest: CpsValueId(16),
                        literal: CpsLiteral::Int("1".to_string()),
                    },
                    CpsStmt::Literal {
                        dest: CpsValueId(17),
                        literal: CpsLiteral::Int("3".to_string()),
                    },
                    CpsStmt::Primitive {
                        dest: CpsValueId(18),
                        op: typed_ir::PrimitiveOp::ListSpliceRaw,
                        args: vec![
                            CpsValueId(10),
                            CpsValueId(16),
                            CpsValueId(17),
                            CpsValueId(15),
                        ],
                    },
                ],
                terminator: CpsTerminator::Return(CpsValueId(18)),
            }],
        };
        let module = CpsModule {
            functions: Vec::new(),
            roots: vec![string_root, list_root],
        };

        validate_cps_module(&module).expect("valid CPS");
        assert_eq!(
            eval_cps_module(&module).expect("evaluated"),
            vec![
                runtime::VmValue::String(runtime::runtime::string_tree::StringTree::from_str(
                    "abcz",
                )),
                runtime::VmValue::List(runtime::runtime::list_tree::ListTree::from_items([
                    Rc::new(runtime::VmValue::Int("1".to_string())),
                    Rc::new(runtime::VmValue::Int("8".to_string())),
                    Rc::new(runtime::VmValue::Int("9".to_string())),
                    Rc::new(runtime::VmValue::Int("4".to_string())),
                ])),
            ]
        );
    }

    #[test]
    fn evaluates_multishot_resumption_with_shared_snapshot() {
        let effect = typed_ir::Path::from_name(typed_ir::Name("choose".to_string()));
        let module = CpsModule {
            functions: Vec::new(),
            roots: vec![CpsFunction {
                name: "root".to_string(),
                params: Vec::new(),
                entry: CpsContinuationId(0),
                handlers: vec![CpsHandler {
                    id: CpsHandlerId(0),
                    arms: vec![CpsHandlerArm {
                        effect: effect.clone(),
                        entry: CpsContinuationId(2),
                    }],
                }],
                continuations: vec![
                    CpsContinuation {
                        id: CpsContinuationId(0),
                        params: Vec::new(),
                        captures: Vec::new(),
                        shot_kind: CpsShotKind::MultiShot,
                        stmts: vec![CpsStmt::Literal {
                            dest: CpsValueId(0),
                            literal: CpsLiteral::Int("1".to_string()),
                        }],
                        terminator: CpsTerminator::Perform {
                            effect,
                            payload: CpsValueId(0),
                            resume: CpsContinuationId(1),
                            handler: CpsHandlerId(0),
                            blocked: None,
                        },
                    },
                    CpsContinuation {
                        id: CpsContinuationId(1),
                        params: vec![CpsValueId(1)],
                        captures: Vec::new(),
                        shot_kind: CpsShotKind::MultiShot,
                        stmts: vec![
                            CpsStmt::Literal {
                                dest: CpsValueId(2),
                                literal: CpsLiteral::Int("10".to_string()),
                            },
                            CpsStmt::Primitive {
                                dest: CpsValueId(3),
                                op: typed_ir::PrimitiveOp::IntAdd,
                                args: vec![CpsValueId(1), CpsValueId(2)],
                            },
                        ],
                        terminator: CpsTerminator::Return(CpsValueId(3)),
                    },
                    CpsContinuation {
                        id: CpsContinuationId(2),
                        params: vec![CpsValueId(4), CpsValueId(5)],
                        captures: Vec::new(),
                        shot_kind: CpsShotKind::MultiShot,
                        stmts: vec![
                            CpsStmt::Literal {
                                dest: CpsValueId(6),
                                literal: CpsLiteral::Int("2".to_string()),
                            },
                            CpsStmt::Resume {
                                dest: CpsValueId(7),
                                resumption: CpsValueId(5),
                                arg: CpsValueId(4),
                            },
                            CpsStmt::Resume {
                                dest: CpsValueId(8),
                                resumption: CpsValueId(5),
                                arg: CpsValueId(6),
                            },
                            CpsStmt::Primitive {
                                dest: CpsValueId(9),
                                op: typed_ir::PrimitiveOp::IntAdd,
                                args: vec![CpsValueId(7), CpsValueId(8)],
                            },
                        ],
                        terminator: CpsTerminator::Return(CpsValueId(9)),
                    },
                ],
            }],
        };

        validate_cps_module(&module).expect("valid CPS");
        assert_eq!(
            eval_cps_module(&module).expect("evaluated"),
            vec![runtime::VmValue::Int("23".to_string())]
        );
    }

    #[test]
    fn evaluates_resumption_under_fresh_handler_stack() {
        let module = rebased_resumption_module();

        validate_cps_module(&module).expect("valid CPS");
        assert_eq!(
            eval_cps_module(&module).expect("evaluated"),
            vec![runtime::VmValue::Int("13".to_string())]
        );
    }

    fn rebased_resumption_module() -> CpsModule {
        let effect = typed_ir::Path::from_name(typed_ir::Name("choose".to_string()));
        CpsModule {
            functions: Vec::new(),
            roots: vec![CpsFunction {
                name: "root".to_string(),
                params: Vec::new(),
                entry: CpsContinuationId(0),
                handlers: vec![
                    CpsHandler {
                        id: CpsHandlerId(0),
                        arms: vec![CpsHandlerArm {
                            effect: effect.clone(),
                            entry: CpsContinuationId(2),
                        }],
                    },
                    CpsHandler {
                        id: CpsHandlerId(1),
                        arms: vec![CpsHandlerArm {
                            effect: effect.clone(),
                            entry: CpsContinuationId(4),
                        }],
                    },
                ],
                continuations: vec![
                    CpsContinuation {
                        id: CpsContinuationId(0),
                        params: Vec::new(),
                        captures: Vec::new(),
                        shot_kind: CpsShotKind::MultiShot,
                        stmts: vec![CpsStmt::Literal {
                            dest: CpsValueId(0),
                            literal: CpsLiteral::Int("1".to_string()),
                        }],
                        terminator: CpsTerminator::Perform {
                            effect: effect.clone(),
                            payload: CpsValueId(0),
                            resume: CpsContinuationId(1),
                            handler: CpsHandlerId(0),
                            blocked: None,
                        },
                    },
                    CpsContinuation {
                        id: CpsContinuationId(1),
                        params: vec![CpsValueId(1)],
                        captures: Vec::new(),
                        shot_kind: CpsShotKind::MultiShot,
                        stmts: vec![CpsStmt::Literal {
                            dest: CpsValueId(2),
                            literal: CpsLiteral::Int("2".to_string()),
                        }],
                        terminator: CpsTerminator::Perform {
                            effect: effect.clone(),
                            payload: CpsValueId(2),
                            resume: CpsContinuationId(3),
                            handler: CpsHandlerId(0),
                            blocked: None,
                        },
                    },
                    CpsContinuation {
                        id: CpsContinuationId(2),
                        params: vec![CpsValueId(4), CpsValueId(5)],
                        captures: Vec::new(),
                        shot_kind: CpsShotKind::MultiShot,
                        stmts: vec![CpsStmt::ResumeWithHandler {
                            dest: CpsValueId(6),
                            resumption: CpsValueId(5),
                            arg: CpsValueId(4),
                            handler: CpsHandlerId(1),
                            envs: Vec::new(),
                        }],
                        terminator: CpsTerminator::Return(CpsValueId(6)),
                    },
                    CpsContinuation {
                        id: CpsContinuationId(3),
                        params: vec![CpsValueId(9)],
                        captures: vec![CpsValueId(1)],
                        shot_kind: CpsShotKind::MultiShot,
                        stmts: vec![CpsStmt::Primitive {
                            dest: CpsValueId(13),
                            op: typed_ir::PrimitiveOp::IntAdd,
                            args: vec![CpsValueId(1), CpsValueId(9)],
                        }],
                        terminator: CpsTerminator::Return(CpsValueId(13)),
                    },
                    CpsContinuation {
                        id: CpsContinuationId(4),
                        params: vec![CpsValueId(7), CpsValueId(8)],
                        captures: Vec::new(),
                        shot_kind: CpsShotKind::MultiShot,
                        stmts: vec![
                            CpsStmt::Literal {
                                dest: CpsValueId(10),
                                literal: CpsLiteral::Int("10".to_string()),
                            },
                            CpsStmt::Primitive {
                                dest: CpsValueId(11),
                                op: typed_ir::PrimitiveOp::IntAdd,
                                args: vec![CpsValueId(7), CpsValueId(10)],
                            },
                            CpsStmt::Resume {
                                dest: CpsValueId(12),
                                resumption: CpsValueId(8),
                                arg: CpsValueId(11),
                            },
                        ],
                        terminator: CpsTerminator::Return(CpsValueId(12)),
                    },
                ],
            }],
        }
    }
}
