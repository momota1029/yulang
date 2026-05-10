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
        }
    }
}

impl std::error::Error for CpsEvalError {}

pub fn eval_cps_module(module: &CpsModule) -> CpsEvalResult<Vec<runtime::VmValue>> {
    module
        .roots
        .iter()
        .map(|root| eval_function(module, root, Vec::new()))
        .collect()
}

fn eval_function(
    module: &CpsModule,
    function: &CpsFunction,
    args: Vec<runtime::VmValue>,
) -> CpsEvalResult<runtime::VmValue> {
    if function.params.len() != args.len() {
        return Err(CpsEvalError::FunctionArgumentMismatch {
            function: function.name.clone(),
            expected: function.params.len(),
            actual: args.len(),
        });
    }
    let value = eval_continuations(
        module,
        function,
        function.entry,
        args.into_iter().map(CpsRuntimeValue::Plain).collect(),
        Vec::new(),
        Vec::new(),
        Vec::new(),
    )?;
    into_plain_value(function, CpsValueId(usize::MAX), value)
}

fn eval_continuations(
    module: &CpsModule,
    function: &CpsFunction,
    entry: CpsContinuationId,
    initial_args: Vec<CpsRuntimeValue>,
    initial_values: Vec<Option<CpsRuntimeValue>>,
    active_handlers: Vec<CpsHandlerFrame>,
    guard_stack: Vec<CpsGuardEntry>,
) -> CpsEvalResult<CpsRuntimeValue> {
    let mut values = initial_values;
    let mut current = entry;
    let mut args = initial_args;
    let mut guard_stack = guard_stack;
    let mut next_guard_id = guard_stack
        .iter()
        .map(|entry| entry.id)
        .max()
        .map_or(0, |id| id + 1);
    loop {
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
                            entry: *entry,
                            values: Rc::new(closure_values),
                        })),
                    );
                }
                CpsStmt::MakeRecursiveClosure { dest, entry } => {
                    let mut closure_values = values.clone();
                    write_value(
                        &mut closure_values,
                        *dest,
                        CpsRuntimeValue::Plain(runtime::VmValue::Unit),
                    );
                    let closure = CpsRuntimeValue::Closure(Rc::new(CpsClosure {
                        entry: *entry,
                        values: Rc::new(closure_values.clone()),
                    }));
                    write_value(&mut closure_values, *dest, closure.clone());
                    write_value(&mut values, *dest, closure);
                }
                CpsStmt::ForceThunk { dest, thunk } => {
                    let value = read_value(function, &values, *thunk)?;
                    let result = match value {
                        CpsRuntimeValue::Thunk(thunk) => eval_continuations(
                            module,
                            function,
                            thunk.entry,
                            Vec::new(),
                            thunk.values.as_ref().clone(),
                            thunk.handlers.as_ref().clone(),
                            thunk.guard_stack.as_ref().clone(),
                        )?,
                        value => value,
                    };
                    write_value(&mut values, *dest, result);
                }
                CpsStmt::Tuple { dest, items } => {
                    let items = items
                        .iter()
                        .map(|id| read_plain_value(function, &values, *id))
                        .collect::<CpsEvalResult<Vec<_>>>()?;
                    write_value(
                        &mut values,
                        *dest,
                        CpsRuntimeValue::Plain(runtime::VmValue::Tuple(items)),
                    );
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
                        .map(|id| read_plain_value(function, &values, id))
                        .transpose()?
                        .map(Box::new);
                    write_value(
                        &mut values,
                        *dest,
                        CpsRuntimeValue::Plain(runtime::VmValue::Variant {
                            tag: tag.clone(),
                            value,
                        }),
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
                    let value = match read_plain_value(function, &values, *tuple)? {
                        runtime::VmValue::Tuple(items) => {
                            items.get(*index).cloned().ok_or_else(|| {
                                CpsEvalError::MissingRecordField {
                                    function: function.name.clone(),
                                    field: core_ir::Name(index.to_string()),
                                }
                            })?
                        }
                        value => value,
                    };
                    write_value(&mut values, *dest, CpsRuntimeValue::Plain(value));
                }
                CpsStmt::VariantTagEq { dest, variant, tag } => {
                    let matches = matches!(
                        read_plain_value(function, &values, *variant)?,
                        runtime::VmValue::Variant { tag: actual, .. } if actual == *tag
                    );
                    write_value(
                        &mut values,
                        *dest,
                        CpsRuntimeValue::Plain(runtime::VmValue::Bool(matches)),
                    );
                }
                CpsStmt::VariantPayload { dest, variant } => {
                    let value = match read_plain_value(function, &values, *variant)? {
                        runtime::VmValue::Variant {
                            value: Some(value), ..
                        } => *value,
                        runtime::VmValue::Variant { value: None, .. } => runtime::VmValue::Unit,
                        value => value,
                    };
                    write_value(&mut values, *dest, CpsRuntimeValue::Plain(value));
                }
                CpsStmt::Primitive { dest, op, args } => {
                    let args = args
                        .iter()
                        .map(|id| read_plain_value(function, &values, *id))
                        .collect::<CpsEvalResult<Vec<_>>>()?;
                    write_value(
                        &mut values,
                        *dest,
                        CpsRuntimeValue::Plain(eval_primitive(*op, &args)?),
                    );
                }
                CpsStmt::DirectCall { dest, target, args } => {
                    let target_function = module
                        .functions
                        .iter()
                        .find(|function| &function.name == target)
                        .ok_or_else(|| CpsEvalError::MissingFunction {
                            name: target.clone(),
                        })?;
                    let args = args
                        .iter()
                        .map(|id| read_plain_value(function, &values, *id))
                        .collect::<CpsEvalResult<Vec<_>>>()?;
                    write_value(
                        &mut values,
                        *dest,
                        CpsRuntimeValue::Plain(eval_function(module, target_function, args)?),
                    );
                }
                CpsStmt::ApplyClosure { dest, closure, arg } => {
                    let closure = read_closure(function, &values, *closure)?;
                    let arg = read_plain_value(function, &values, *arg)?;
                    let result = eval_continuations(
                        module,
                        function,
                        closure.entry,
                        vec![CpsRuntimeValue::Plain(arg)],
                        closure.values.as_ref().clone(),
                        active_handlers.clone(),
                        guard_stack.clone(),
                    )?;
                    write_value(&mut values, *dest, result);
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
                    let result = eval_continuations(
                        module,
                        function,
                        resumption.target,
                        vec![CpsRuntimeValue::Plain(arg)],
                        resumption.values.as_ref().clone(),
                        resumption.handlers.as_ref().clone(),
                        resumption.guard_stack.as_ref().clone(),
                    )?;
                    write_value(&mut values, *dest, result);
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
                    let result = eval_continuations(
                        module,
                        function,
                        resumption.target,
                        vec![CpsRuntimeValue::Plain(arg)],
                        resumption.values.as_ref().clone(),
                        handler_stack_with_pushed(
                            resumption.handlers.as_ref(),
                            *handler,
                            &guard_stack,
                            envs,
                        ),
                        resumption.guard_stack.as_ref().clone(),
                    )?;
                    write_value(&mut values, *dest, result);
                }
            }
        }

        match &continuation.terminator {
            CpsTerminator::Return(value) => return read_value(function, &values, *value),
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
                let payload = read_plain_value(function, &values, *payload)?;
                let blocked = blocked
                    .map(|blocked| read_effect_id(function, &values, blocked))
                    .transpose()?;
                let handler_stack =
                    handler_stack_with_static(&active_handlers, *handler, &guard_stack);
                let (handler, frame, handler_body_stack) =
                    handler_arm_for_stack(function, &handler_stack, effect, blocked)?;
                let handler_values = values_with_handler_env(values.clone(), frame, handler.entry);
                let resumption = CpsRuntimeValue::Resumption(Rc::new(CpsResumption {
                    target: *resume,
                    values: Rc::new(values.clone()),
                    handlers: Rc::new(handler_stack.clone()),
                    guard_stack: Rc::new(guard_stack.clone()),
                }));
                return eval_continuations(
                    module,
                    function,
                    handler.entry,
                    vec![CpsRuntimeValue::Plain(payload), resumption],
                    handler_values,
                    handler_body_stack,
                    guard_stack,
                );
            }
        }
    }
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
    function: &'a CpsFunction,
    stack: &'a [CpsHandlerFrame],
    effect: &core_ir::Path,
    blocked: Option<u64>,
) -> CpsEvalResult<(&'a CpsHandlerArm, &'a CpsHandlerFrame, Vec<CpsHandlerFrame>)> {
    for (index, frame) in stack.iter().enumerate().rev() {
        if blocked.is_some_and(|blocked| frame.guard_stack.iter().any(|entry| entry.id == blocked))
        {
            continue;
        }
        if let Some(arm) = function
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
            return Ok((arm, frame, stack[..index].to_vec()));
        }
    }
    Err(CpsEvalError::MissingHandler {
        function: function.name.clone(),
        id: stack.last().expect("handler stack is non-empty").handler,
    })
}

fn handler_stack_with_static(
    active_handlers: &[CpsHandlerFrame],
    fallback: CpsHandlerId,
    guard_stack: &[CpsGuardEntry],
) -> Vec<CpsHandlerFrame> {
    if active_handlers.is_empty() {
        vec![CpsHandlerFrame {
            handler: fallback,
            guard_stack: guard_stack.to_vec(),
            envs: Vec::new(),
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
        handler,
        guard_stack: guard_stack.to_vec(),
        envs,
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
    match value {
        CpsRuntimeValue::Plain(value) => Ok(value),
        CpsRuntimeValue::Resumption(_)
        | CpsRuntimeValue::Thunk(_)
        | CpsRuntimeValue::Closure(_) => Err(CpsEvalError::ExpectedPlainValue {
            function: function.name.clone(),
            id,
        }),
    }
}

fn read_resumption(
    function: &CpsFunction,
    values: &[Option<CpsRuntimeValue>],
    id: CpsValueId,
) -> CpsEvalResult<Rc<CpsResumption>> {
    match read_value(function, values, id)? {
        CpsRuntimeValue::Resumption(resumption) => Ok(resumption),
        CpsRuntimeValue::Plain(_) | CpsRuntimeValue::Thunk(_) | CpsRuntimeValue::Closure(_) => {
            Err(CpsEvalError::ExpectedResumption {
                function: function.name.clone(),
                id,
            })
        }
    }
}

fn read_closure(
    function: &CpsFunction,
    values: &[Option<CpsRuntimeValue>],
    id: CpsValueId,
) -> CpsEvalResult<Rc<CpsClosure>> {
    match read_value(function, values, id)? {
        CpsRuntimeValue::Closure(closure) => Ok(closure),
        CpsRuntimeValue::Plain(_) | CpsRuntimeValue::Resumption(_) | CpsRuntimeValue::Thunk(_) => {
            Err(CpsEvalError::ExpectedPlainValue {
                function: function.name.clone(),
                id,
            })
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
enum CpsRuntimeValue {
    Plain(runtime::VmValue),
    Resumption(Rc<CpsResumption>),
    Thunk(Rc<CpsThunk>),
    Closure(Rc<CpsClosure>),
}

#[derive(Debug, Clone, PartialEq)]
struct CpsResumption {
    target: CpsContinuationId,
    values: Rc<Vec<Option<CpsRuntimeValue>>>,
    handlers: Rc<Vec<CpsHandlerFrame>>,
    guard_stack: Rc<Vec<CpsGuardEntry>>,
}

#[derive(Debug, Clone, PartialEq)]
struct CpsThunk {
    entry: CpsContinuationId,
    values: Rc<Vec<Option<CpsRuntimeValue>>>,
    handlers: Rc<Vec<CpsHandlerFrame>>,
    guard_stack: Rc<Vec<CpsGuardEntry>>,
}

#[derive(Debug, Clone, PartialEq)]
struct CpsClosure {
    entry: CpsContinuationId,
    values: Rc<Vec<Option<CpsRuntimeValue>>>,
}

#[derive(Debug, Clone, PartialEq)]
struct CpsHandlerFrame {
    handler: CpsHandlerId,
    guard_stack: Vec<CpsGuardEntry>,
    envs: Vec<CpsEvaluatedHandlerEnv>,
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
