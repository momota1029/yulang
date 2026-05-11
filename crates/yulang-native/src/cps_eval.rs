use std::collections::BTreeMap;
use std::fmt;
use std::rc::Rc;

use yulang_core_ir as core_ir;
use yulang_runtime as runtime;

use crate::cps_ir::{
    CpsContinuation, CpsContinuationId, CpsFunction, CpsHandlerArm, CpsHandlerEnv, CpsHandlerId,
    CpsLiteral, CpsModule, CpsStmt, CpsTerminator, CpsValueId,
};

pub type CpsEvalResult<T> = Result<T, CpsEvalError>;

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
            format!("Thunk(owner={}, entry={:?})", thunk.owner_function, thunk.entry)
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
        CpsRuntimeValue::Variant { tag, value } => match value {
            Some(value) => format!("Variant({}, {})", tag.0, summarize_cps_value(value)),
            None => format!("Variant({})", tag.0),
        },
        CpsRuntimeValue::ScopeReturn { prompt, target, value } => format!(
            "ScopeReturn(prompt={}, target={:?}, value={})",
            prompt.0, target, summarize_cps_value(value),
        ),
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
        op: core_ir::PrimitiveOp,
    },
    PrimitiveTypeMismatch {
        op: core_ir::PrimitiveOp,
        value: runtime::VmValue,
    },
    InvalidPrimitiveArity {
        op: core_ir::PrimitiveOp,
        expected: usize,
        actual: usize,
    },
    ExpectedRecord {
        function: String,
        value: runtime::VmValue,
    },
    MissingRecordField {
        function: String,
        field: core_ir::Name,
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
            let value = eval_function(module, root, Vec::new())?;
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
            into_plain_value(root, CpsValueId(usize::MAX), value)
        })
        .collect()
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
                let frame_owner_match = target == EXIT_RWH_TARGET
                    || frame.escape_owner_function == current_function;
                let frame_owner = frame.escape_owner_function.clone();
                let frame_install_eval = frame.install_eval_id;
                let threshold = frame.return_frame_threshold;
                if !frame_owner_match {
                    trace_cps(
                        "ScopeReturnDispatch",
                        format!(
                            "fn={} eval={} prompt={} target={:?} matched=yes install_eval={} owner={} owner_match=no action=Propagate",
                            current_function, current_eval_id.0, prompt.0, target,
                            frame_install_eval.0, frame_owner,
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
                        current_function, current_eval_id.0, prompt.0, target,
                        frame_install_eval.0, frame_owner, threshold,
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
    initial_frame_count: usize,
    current_eval_id: CpsEvalId,
) -> CpsEvalResult<CpsRuntimeValue> {
    let mut values = initial_values;
    let mut current = entry;
    let mut args = initial_args;
    let mut guard_stack = guard_stack;
    let mut active_handlers = active_handlers;
    let mut return_frames = return_frames;
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
            match handle_scope_return(
                $result,
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
                ScopeReturnAction::Propagate(v) => return Ok(v),
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
                        })),
                    );
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
                                let owner =
                                    function_by_name(module, &thunk.owner_function)?;
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
                CpsStmt::Record { dest, fields } => {
                    let mut record = BTreeMap::new();
                    for field in fields {
                        record.insert(
                            field.name.clone(),
                            read_plain_value(function, &values, field.value)?,
                        );
                    }
                    write_value(
                        &mut values,
                        *dest,
                        CpsRuntimeValue::Plain(runtime::VmValue::Record(record)),
                    );
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
                    let value = match read_plain_value(function, &values, *base)? {
                        runtime::VmValue::Record(fields) => {
                            fields.get(field).cloned().ok_or_else(|| {
                                CpsEvalError::MissingRecordField {
                                    function: function.name.clone(),
                                    field: field.clone(),
                                }
                            })?
                        }
                        value => {
                            return Err(CpsEvalError::ExpectedRecord {
                                function: function.name.clone(),
                                value,
                            });
                        }
                    };
                    write_value(&mut values, *dest, CpsRuntimeValue::Plain(value));
                }
                CpsStmt::TupleGet { dest, tuple, index } => {
                    let value = match read_value(function, &values, *tuple)? {
                        CpsRuntimeValue::Tuple(items) => items
                            .get(*index)
                            .cloned()
                            .ok_or_else(|| CpsEvalError::MissingRecordField {
                                function: function.name.clone(),
                                field: core_ir::Name(index.to_string()),
                            })?,
                        CpsRuntimeValue::Plain(runtime::VmValue::Tuple(items)) => {
                            cps_value_from_vm(items.get(*index).cloned().ok_or_else(|| {
                                CpsEvalError::MissingRecordField {
                                    function: function.name.clone(),
                                    field: core_ir::Name(index.to_string()),
                                }
                            })?)
                        }
                        other => other,
                    };
                    write_value(&mut values, *dest, value);
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
                        core_ir::PrimitiveOp::ListEmpty
                            | core_ir::PrimitiveOp::ListSingleton
                            | core_ir::PrimitiveOp::ListMerge
                            | core_ir::PrimitiveOp::ListLen
                            | core_ir::PrimitiveOp::ListIndex
                            | core_ir::PrimitiveOp::ListIndexRangeRaw
                    ) {
                        trace_cps(
                            "PrimitiveList",
                            format!(
                                "fn={} cont={:?} op={:?} args=[{}] result={}",
                                function.name, current, op,
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
                CpsStmt::DirectCall { dest, target, args: arg_ids } => {
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
                            function.name, current,
                            summarize_cps_value(&callable),
                            arg_preview,
                            return_frames.len(), initial_frame_count,
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
                                inherited,
                            )?
                        }
                        CpsRuntimeValue::Resumption(resumption) => {
                            // Treat as Resume: the surface saw an opaque
                            // callable, but the runtime value is a captured
                            // continuation. Resume needs a plain payload.
                            let arg = read_plain_value(function, &values, *arg)?;
                            let owner = function_by_name(module, &resumption.owner_function)?;
                            let resumed_handlers = merge_resumption_handlers(
                                resumption.handlers.as_ref(),
                                &active_handlers,
                            );
                            let adjusted_frames = merge_extras_into_frames(
                                resumption.return_frames.as_ref(),
                                &active_handlers,
                            );
                            trace_cps(
                                "ResumeHandlerMerge",
                                format!(
                                    "site=ApplyClosure(Resumption) fn={} eval={} captured={} current={} merged={}",
                                    function.name,
                                    current_eval_id.0,
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
                    let resumed_handlers = merge_resumption_handlers(
                        resumption.handlers.as_ref(),
                        &active_handlers,
                    );
                    let adjusted_frames = merge_extras_into_frames(
                        resumption.return_frames.as_ref(),
                        &active_handlers,
                    );
                    trace_cps(
                        "ResumeHandlerMerge",
                        format!(
                            "site=Resume fn={} eval={} captured={} current={} merged={}",
                            function.name,
                            current_eval_id.0,
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
                        0,
                    )?;
                    dispatch_scope_return!('cont, result, dest);
                }
                CpsStmt::InstallHandler {
                    handler,
                    envs,
                    escape,
                } => {
                    let envs = capture_handler_envs(function, &values, envs)?;
                    let pushed_prompt = fresh_prompt();
                    let threshold = return_frames.len();
                    active_handlers.push(CpsHandlerFrame {
                        prompt: pushed_prompt,
                        handler: *handler,
                        guard_stack: guard_stack.clone(),
                        envs,
                        escape: *escape,
                        escape_owner_function: function.name.clone(),
                        inherited: false,
                        return_frame_threshold: threshold,
                        install_eval_id: current_eval_id,
                    });
                    trace_cps(
                        "InstallHandler",
                        format!(
                            "fn={} eval={} cont={:?} handler={:?} prompt={} escape={:?} threshold={} handlers.now={}",
                            function.name, current_eval_id.0, current, handler,
                            pushed_prompt.0, escape, threshold, active_handlers.len(),
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
                    let envs = capture_handler_envs(function, &values, envs)?;
                    let owner = function_by_name(module, &resumption.owner_function)?;
                    // Push the RWH-installed frame onto our own active_handlers
                    // (non-inherited, sentinel-target) so a ScopeReturn that
                    // matches the freshly-installed handler resolves at this
                    // very call site rather than escaping the eval frame.
                    let pushed_prompt = fresh_prompt();
                    active_handlers.push(CpsHandlerFrame {
                        prompt: pushed_prompt,
                        handler: *handler,
                        guard_stack: guard_stack.clone(),
                        envs,
                        escape: EXIT_RWH_TARGET,
                        escape_owner_function: function.name.clone(),
                        inherited: false,
                        return_frame_threshold: return_frames.len(),
                        install_eval_id: current_eval_id,
                    });
                    // RWH uses REBASED semantics: the just-installed handler
                    // SHADOWS the captured innermost handler. So inner_handlers
                    // = captured ++ [RWH-pushed], with RWH innermost. This is
                    // different from regular Resume merge (which preserves
                    // captured innermost). Tested by
                    // `evaluates_resumption_under_fresh_handler_stack`.
                    let inner_handlers = {
                        let mut stack = resumption.handlers.as_ref().clone();
                        let mut owned = active_handlers
                            .last()
                            .cloned()
                            .expect("just pushed RWH frame");
                        owned.inherited = true;
                        stack.push(owned);
                        stack
                    };
                    let pushed_extra = active_handlers
                        .iter()
                        .filter(|f| f.prompt == pushed_prompt)
                        .cloned()
                        .collect::<Vec<_>>();
                    // For frame injection, we still use the OLD inject helper
                    // (append RWH frame to each captured frame's handlers,
                    // since RWH frame is innermost in the merged stack).
                    let adjusted_frames = inject_extra_handlers_legacy(
                        resumption.return_frames.as_ref(),
                        &pushed_extra,
                    );
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
                        function.name, current, summarize_cps_value(&v),
                        return_frames.len(), initial_frame_count,
                    ),
                );
                if return_frames.len() <= initial_frame_count {
                    return Ok(v);
                }
                // write23 Step 3 / write17 v2: if Returning a Thunk and the
                // top own-frame's continuation immediately ForceThunks its
                // param, run that continuation in the top frame's owner
                // context (function = frame.owner_function, eval_id =
                // frame.owner_eval_id) with ALL return_frames retained as
                // inherited. This keeps the post-call frame (e.g.
                // F_each_post) in scope while the deferred body runs, so
                // a `Perform` inside the body captures it. With write22's
                // strict install_eval_id check, a `ScopeReturn` raised in
                // the body can resolve handlers installed at the frame's
                // owner eval.
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
                current = if bool_value(core_ir::PrimitiveOp::BoolNot, &cond)? {
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
                        function.name, current_eval_id.0, current, effect,
                        return_frames.len(), initial_frame_count,
                        summarize_handler_stack(&active_handlers),
                    ),
                );
                let payload = read_plain_value(function, &values, *payload)?;
                let blocked = blocked
                    .map(|blocked| read_effect_id(function, &values, blocked))
                    .transpose()?;
                let handler_stack =
                    handler_stack_with_static(&active_handlers, *handler, &guard_stack);
                let (handler_arm, frame, handler_body_stack, handler_owner) =
                    handler_arm_for_stack(module, function, &handler_stack, effect, blocked)?;
                let handler_values =
                    values_with_handler_env(Vec::new(), frame, handler_arm.entry);
                let resumption = CpsRuntimeValue::Resumption(Rc::new(CpsResumption {
                    owner_function: function.name.clone(),
                    target: *resume,
                    values: Rc::new(values.clone()),
                    handlers: Rc::new(handler_stack.clone()),
                    guard_stack: Rc::new(guard_stack.clone()),
                    return_frames: Rc::new(return_frames.clone()),
                }));
                // Detect whether the chosen handler frame is in our local
                // `active_handlers` (so its prompt will match on dispatch)
                // or whether it was synthesized by `handler_stack_with_static`
                // because we had no installed handlers at all. In the
                // synthetic case the arm's result must just become the
                // perform-frame's return value, with no ScopeReturn wrapping.
                let frame_prompt = frame.prompt;
                let frame_escape = frame.escape;
                let frame_in_active = active_handlers
                    .iter()
                    .any(|f| f.prompt == frame_prompt);
                let result = eval_continuations(
                    module,
                    handler_owner,
                    handler_arm.entry,
                    vec![CpsRuntimeValue::Plain(payload), resumption],
                    handler_values,
                    handler_body_stack,
                    guard_stack.clone(),
                    Vec::new(),
                    0,
                )?;
                if !frame_in_active {
                    // Synthetic fallback frame: the perform's effect had no
                    // installed handler in this eval, so the arm's result is
                    // the value of *this* eval frame.
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
                    ScopeReturnAction::JumpOrExit { target, value, return_frame_threshold } => {
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
                    ScopeReturnAction::Propagate(v) => {
                        return Ok(v);
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
                    owner_function: function.name.clone(),
                    continuation: *resume,
                    values: Rc::new(values.clone()),
                    active_handlers: active_handlers.clone(),
                    guard_stack: guard_stack.clone(),
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
                            owner_function: function.name.clone(),
                            continuation: *resume,
                            values: Rc::new(values.clone()),
                            active_handlers: active_handlers.clone(),
                            guard_stack: guard_stack.clone(),
                            owner_initial_frame_count: initial_frame_count,
                            owner_eval_id: current_eval_id,
                        };
                        let mut new_frames = return_frames.clone();
                        new_frames.push(frame);
                        let owner =
                            function_by_name(module, &thunk_rc.owner_function)?;
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
                        function.name, current,
                        summarize_cps_value(&callable),
                        arg_preview,
                        resume, return_frames.len(), initial_frame_count,
                    ),
                );
                let pre_push_count = return_frames.len();
                let frame = CpsReturnFrame {
                    owner_function: function.name.clone(),
                    continuation: *resume,
                    values: Rc::new(values.clone()),
                    active_handlers: active_handlers.clone(),
                    guard_stack: guard_stack.clone(),
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
                        let resumed_handlers = merge_resumption_handlers(
                            resumption.handlers.as_ref(),
                            &active_handlers,
                        );
                        let adjusted_res = merge_extras_into_frames(
                            resumption.return_frames.as_ref(),
                            &active_handlers,
                        );
                        trace_cps(
                            "ResumeHandlerMerge",
                            format!(
                                "site=EffectfulApply(Resumption) fn={} eval={} captured={} current={} merged={}",
                                function.name,
                                current_eval_id.0,
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

/// Merge a captured continuation's handler stack with the resume site's
/// current handler stack.
///
/// Semantics (write23): handlers installed at the resume site (after the
/// original capture) are siblings to the captured continuation's outer
/// scope — they belong OUTSIDE the captured continuation's inner handlers,
/// not innermost-of-all. Concretely:
///
/// ```text
/// captured = [outer, H_sub]              (e.g. branch perform capture)
/// current  = [outer, H_inner]            (recursive once installed H_inner)
/// merged   = [outer, H_inner, H_sub]
/// ```
///
/// The shared outer prefix is identified by (prompt, install_eval_id)
/// equality. Resume-site handlers after that prefix (and not duplicated in
/// `captured`) are placed BEFORE the captured continuation's inner tail,
/// so when ScopeReturn truncates at the captured inner handler, the
/// resume-site siblings survive.
fn merge_resumption_handlers(
    captured: &[CpsHandlerFrame],
    current: &[CpsHandlerFrame],
) -> Vec<CpsHandlerFrame> {
    let mut shared = 0;
    while shared < captured.len()
        && shared < current.len()
        && captured[shared].prompt == current[shared].prompt
        && captured[shared].install_eval_id == current[shared].install_eval_id
    {
        shared += 1;
    }

    let mut merged = Vec::with_capacity(captured.len() + current.len());
    merged.extend(captured[..shared].iter().cloned());

    for frame in &current[shared..] {
        if !captured.iter().any(|c| {
            c.prompt == frame.prompt && c.install_eval_id == frame.install_eval_id
        }) {
            merged.push(frame.clone());
        }
    }

    merged.extend(captured[shared..].iter().cloned());
    merged
}

/// Legacy inject helper kept for `ResumeWithHandler` (rebased semantics):
/// the just-installed RWH frame is appended to each captured frame's
/// handler stack as the innermost handler. Different from
/// `merge_extras_into_frames` which preserves captured innermost.
fn inject_extra_handlers_legacy(
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
/// the resume site's live handler stack. The result is a fresh return
/// frame list with each frame's handler stack reconciled so the
/// resume-site siblings sit outside the captured inner handlers.
fn merge_extras_into_frames(
    frames: &[CpsReturnFrame],
    current: &[CpsHandlerFrame],
) -> Vec<CpsReturnFrame> {
    frames
        .iter()
        .map(|frame| {
            let merged = merge_resumption_handlers(&frame.active_handlers, current);
            if trace_enabled() && merged != frame.active_handlers {
                trace_cps(
                    "InjectExtraHandlers",
                    format!(
                        "frame_owner={} frame_owner_eval={} before={} current={} after={}",
                        frame.owner_function,
                        frame.owner_eval_id.0,
                        summarize_handler_stack(&frame.active_handlers),
                        summarize_handler_stack(current),
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
    if matches!(value, CpsRuntimeValue::ScopeReturn { .. }) {
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
            frame.owner_function, frame.continuation, frame.owner_eval_id.0,
            rest.len(), frame.owner_initial_frame_count,
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
        owner_initial,
        frame.owner_eval_id,
    )
}

fn function_by_name<'a>(
    module: &'a CpsModule,
    name: &str,
) -> CpsEvalResult<&'a CpsFunction> {
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

fn handler_arm_for_stack<'a>(
    module: &'a CpsModule,
    current_function: &'a CpsFunction,
    stack: &'a [CpsHandlerFrame],
    effect: &core_ir::Path,
    blocked: Option<u64>,
) -> CpsEvalResult<(
    &'a CpsHandlerArm,
    &'a CpsHandlerFrame,
    Vec<CpsHandlerFrame>,
    &'a CpsFunction,
)> {
    for (index, frame) in stack.iter().enumerate().rev() {
        if blocked.is_some_and(|blocked| frame.guard_stack.iter().any(|entry| entry.id == blocked))
        {
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
            for value in &env.values {
                values_by_id.push((*value, read_value(function, values, *value)?));
            }
            Ok(CpsEvaluatedHandlerEnv {
                entry: env.entry,
                values: values_by_id,
            })
        })
        .collect()
}

fn values_with_handler_env(
    mut values: Vec<Option<CpsRuntimeValue>>,
    frame: &CpsHandlerFrame,
    entry: CpsContinuationId,
) -> Vec<Option<CpsRuntimeValue>> {
    let Some(env) = frame.envs.iter().find(|env| env.entry == entry) else {
        return values;
    };
    for (id, value) in &env.values {
        write_value(&mut values, *id, value.clone());
    }
    values
}

fn effect_matches(expected: &core_ir::Path, actual: &core_ir::Path) -> bool {
    actual == expected
        || (!expected.segments.is_empty()
            && actual.segments.len() == expected.segments.len() + 1
            && actual.segments.starts_with(&expected.segments))
        || (expected.segments.len() == 1 && actual.segments.last() == expected.segments.first())
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
    Variant {
        tag: core_ir::Name,
        value: Option<Box<CpsRuntimeValue>>,
    },
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

#[derive(Debug, Clone, PartialEq)]
struct CpsResumption {
    owner_function: String,
    target: CpsContinuationId,
    values: Rc<Vec<Option<CpsRuntimeValue>>>,
    handlers: Rc<Vec<CpsHandlerFrame>>,
    guard_stack: Rc<Vec<CpsGuardEntry>>,
    /// Stack of return frames representing caller continuations that were
    /// suspended waiting for this resumption. When the resumption is resumed,
    /// its local continuation runs first; if it returns normally the frames
    /// are continued in order (innermost first).
    return_frames: Rc<Vec<CpsReturnFrame>>,
}

/// A suspended caller continuation. Pushed by effectful terminators
/// (EffectfulCall / EffectfulApply / EffectfulForce) when a potentially-
/// effectful call is made inside a handler scope. Stored in
/// `CpsResumption.return_frames` so that resuming k also resumes the
/// caller's computation after the call.
#[derive(Debug, Clone, PartialEq)]
struct CpsReturnFrame {
    owner_function: String,
    continuation: CpsContinuationId,
    values: Rc<Vec<Option<CpsRuntimeValue>>>,
    /// Handler snapshot at the effectful-call site, BEFORE the callee's
    /// `into_inherited` pass. Restored as-is (non-inherited frames remain
    /// non-inherited) when the frame is re-entered via `continue_return_frames`.
    active_handlers: Vec<CpsHandlerFrame>,
    guard_stack: Vec<CpsGuardEntry>,
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
struct CpsThunk {
    owner_function: String,
    entry: CpsContinuationId,
    values: Rc<Vec<Option<CpsRuntimeValue>>>,
    handlers: Rc<Vec<CpsHandlerFrame>>,
    guard_stack: Rc<Vec<CpsGuardEntry>>,
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
    op: core_ir::PrimitiveOp,
    args: Vec<CpsRuntimeValue>,
) -> CpsEvalResult<CpsRuntimeValue> {
    use core_ir::PrimitiveOp;
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

fn cps_value_to_usize(
    op: core_ir::PrimitiveOp,
    value: CpsRuntimeValue,
) -> CpsEvalResult<usize> {
    match value {
        CpsRuntimeValue::Plain(runtime::VmValue::Int(s)) => s
            .parse::<usize>()
            .map_err(|_| CpsEvalError::UnsupportedPrimitive { op }),
        _ => Err(CpsEvalError::UnsupportedPrimitive { op }),
    }
}

fn control_list_items(
    op: core_ir::PrimitiveOp,
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
    op: core_ir::PrimitiveOp,
    args: &[runtime::VmValue],
) -> CpsEvalResult<runtime::VmValue> {
    use core_ir::PrimitiveOp;
    match op {
        PrimitiveOp::BoolNot => {
            expect_arity(op, args, 1)?;
            Ok(runtime::VmValue::Bool(!bool_value(op, &args[0])?))
        }
        PrimitiveOp::BoolEq => {
            expect_arity(op, args, 2)?;
            Ok(runtime::VmValue::Bool(
                bool_value(op, &args[0])? == bool_value(op, &args[1])?,
            ))
        }
        PrimitiveOp::IntAdd => int_bin_op(op, args, |left, right| left + right),
        PrimitiveOp::IntSub => int_bin_op(op, args, |left, right| left - right),
        PrimitiveOp::IntMul => int_bin_op(op, args, |left, right| left * right),
        PrimitiveOp::IntDiv => int_bin_op(op, args, |left, right| left / right),
        PrimitiveOp::IntEq => int_cmp_op(op, args, |left, right| left == right),
        PrimitiveOp::IntLt => int_cmp_op(op, args, |left, right| left < right),
        PrimitiveOp::IntLe => int_cmp_op(op, args, |left, right| left <= right),
        PrimitiveOp::IntGt => int_cmp_op(op, args, |left, right| left > right),
        PrimitiveOp::IntGe => int_cmp_op(op, args, |left, right| left >= right),
        PrimitiveOp::FloatAdd => float_bin_op(op, args, |left, right| left + right),
        PrimitiveOp::FloatSub => float_bin_op(op, args, |left, right| left - right),
        PrimitiveOp::FloatMul => float_bin_op(op, args, |left, right| left * right),
        PrimitiveOp::FloatDiv => float_bin_op(op, args, |left, right| left / right),
        PrimitiveOp::FloatEq => float_cmp_op(op, args, |left, right| left == right),
        PrimitiveOp::FloatLt => float_cmp_op(op, args, |left, right| left < right),
        PrimitiveOp::FloatLe => float_cmp_op(op, args, |left, right| left <= right),
        PrimitiveOp::FloatGt => float_cmp_op(op, args, |left, right| left > right),
        PrimitiveOp::FloatGe => float_cmp_op(op, args, |left, right| left >= right),
        PrimitiveOp::StringConcat => {
            expect_arity(op, args, 2)?;
            let left = string_value(op, &args[0])?;
            let right = string_value(op, &args[1])?;
            Ok(runtime::VmValue::String(
                runtime::runtime::string_tree::StringTree::concat(left.clone(), right.clone()),
            ))
        }
        PrimitiveOp::IntToString => {
            expect_arity(op, args, 1)?;
            Ok(value_from_string(&int_value(op, &args[0])?.to_string()))
        }
        PrimitiveOp::FloatToString => {
            expect_arity(op, args, 1)?;
            Ok(value_from_string(&format_float_value(float_value(
                op, &args[0],
            )?)))
        }
        PrimitiveOp::BoolToString => {
            expect_arity(op, args, 1)?;
            Ok(value_from_string(if bool_value(op, &args[0])? {
                "true"
            } else {
                "false"
            }))
        }
        _ => runtime::vm::primitive::apply_primitive(op, args).map_err(|_| {
            CpsEvalError::UnsupportedPrimitive { op }
        }),
    }
}

fn int_bin_op(
    op: core_ir::PrimitiveOp,
    args: &[runtime::VmValue],
    f: impl FnOnce(i64, i64) -> i64,
) -> CpsEvalResult<runtime::VmValue> {
    expect_arity(op, args, 2)?;
    Ok(runtime::VmValue::Int(
        f(int_value(op, &args[0])?, int_value(op, &args[1])?).to_string(),
    ))
}

fn int_cmp_op(
    op: core_ir::PrimitiveOp,
    args: &[runtime::VmValue],
    f: impl FnOnce(i64, i64) -> bool,
) -> CpsEvalResult<runtime::VmValue> {
    expect_arity(op, args, 2)?;
    Ok(runtime::VmValue::Bool(f(
        int_value(op, &args[0])?,
        int_value(op, &args[1])?,
    )))
}

fn float_bin_op(
    op: core_ir::PrimitiveOp,
    args: &[runtime::VmValue],
    f: impl FnOnce(f64, f64) -> f64,
) -> CpsEvalResult<runtime::VmValue> {
    expect_arity(op, args, 2)?;
    Ok(runtime::VmValue::Float(format_float_value(f(
        float_value(op, &args[0])?,
        float_value(op, &args[1])?,
    ))))
}

fn float_cmp_op(
    op: core_ir::PrimitiveOp,
    args: &[runtime::VmValue],
    f: impl FnOnce(f64, f64) -> bool,
) -> CpsEvalResult<runtime::VmValue> {
    expect_arity(op, args, 2)?;
    Ok(runtime::VmValue::Bool(f(
        float_value(op, &args[0])?,
        float_value(op, &args[1])?,
    )))
}

fn expect_arity(
    op: core_ir::PrimitiveOp,
    args: &[runtime::VmValue],
    expected: usize,
) -> CpsEvalResult<()> {
    if args.len() == expected {
        Ok(())
    } else {
        Err(CpsEvalError::InvalidPrimitiveArity {
            op,
            expected,
            actual: args.len(),
        })
    }
}

fn int_value(op: core_ir::PrimitiveOp, value: &runtime::VmValue) -> CpsEvalResult<i64> {
    match value {
        runtime::VmValue::Int(value) => {
            value
                .parse()
                .map_err(|_| CpsEvalError::PrimitiveTypeMismatch {
                    op,
                    value: value_from_string(value),
                })
        }
        value => Err(CpsEvalError::PrimitiveTypeMismatch {
            op,
            value: value.clone(),
        }),
    }
}

fn float_value(op: core_ir::PrimitiveOp, value: &runtime::VmValue) -> CpsEvalResult<f64> {
    match value {
        runtime::VmValue::Float(value) => {
            value
                .parse()
                .map_err(|_| CpsEvalError::PrimitiveTypeMismatch {
                    op,
                    value: runtime::VmValue::Float(value.clone()),
                })
        }
        value => Err(CpsEvalError::PrimitiveTypeMismatch {
            op,
            value: value.clone(),
        }),
    }
}

fn bool_value(op: core_ir::PrimitiveOp, value: &runtime::VmValue) -> CpsEvalResult<bool> {
    match value {
        runtime::VmValue::Bool(value) => Ok(*value),
        value => Err(CpsEvalError::PrimitiveTypeMismatch {
            op,
            value: value.clone(),
        }),
    }
}

fn string_value(
    op: core_ir::PrimitiveOp,
    value: &runtime::VmValue,
) -> CpsEvalResult<&runtime::runtime::string_tree::StringTree> {
    match value {
        runtime::VmValue::String(value) => Ok(value),
        value => Err(CpsEvalError::PrimitiveTypeMismatch {
            op,
            value: value.clone(),
        }),
    }
}

fn format_float_value(value: f64) -> String {
    let mut rendered = value.to_string();
    if !rendered.contains('.') && !rendered.contains('e') && !rendered.contains('E') {
        rendered.push_str(".0");
    }
    rendered
}

fn value_from_string(value: &str) -> runtime::VmValue {
    runtime::VmValue::String(runtime::runtime::string_tree::StringTree::from_str(value))
}

#[cfg(test)]
mod tests {
    use crate::cps_ir::{
        CpsContinuation, CpsContinuationId, CpsFunction, CpsHandler, CpsHandlerArm, CpsHandlerId,
        CpsLiteral, CpsModule, CpsShotKind, CpsStmt, CpsTerminator, CpsValueId,
    };
    use crate::cps_validate::validate_cps_module;

    use super::*;

    #[test]
    fn evaluates_multishot_resumption_with_shared_snapshot() {
        let effect = core_ir::Path::from_name(core_ir::Name("choose".to_string()));
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
                                op: core_ir::PrimitiveOp::IntAdd,
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
                                op: core_ir::PrimitiveOp::IntAdd,
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
        let effect = core_ir::Path::from_name(core_ir::Name("choose".to_string()));
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
                            op: core_ir::PrimitiveOp::IntAdd,
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
                                op: core_ir::PrimitiveOp::IntAdd,
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
