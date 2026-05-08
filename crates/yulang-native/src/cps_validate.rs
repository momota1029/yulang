use std::collections::HashSet;
use std::fmt;

use crate::cps_ir::{
    CpsContinuation, CpsContinuationId, CpsFunction, CpsHandlerId, CpsModule, CpsStmt,
    CpsTerminator, CpsValueId,
};

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CpsValidateError {
    MissingEntry {
        function: String,
        entry: CpsContinuationId,
    },
    DuplicateContinuation {
        function: String,
        id: CpsContinuationId,
    },
    MissingContinuation {
        function: String,
        id: CpsContinuationId,
    },
    DuplicateHandler {
        function: String,
        id: CpsHandlerId,
    },
    MissingHandler {
        function: String,
        id: CpsHandlerId,
    },
    ContinuationArityMismatch {
        function: String,
        id: CpsContinuationId,
        expected: usize,
        actual: usize,
    },
    MissingValue {
        function: String,
        id: CpsValueId,
    },
}

impl fmt::Display for CpsValidateError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            CpsValidateError::MissingEntry { function, entry } => {
                write!(
                    f,
                    "CPS function {function} has no entry continuation {entry:?}"
                )
            }
            CpsValidateError::DuplicateContinuation { function, id } => {
                write!(
                    f,
                    "CPS function {function} defines continuation {id:?} twice"
                )
            }
            CpsValidateError::MissingContinuation { function, id } => {
                write!(
                    f,
                    "CPS function {function} references missing continuation {id:?}"
                )
            }
            CpsValidateError::DuplicateHandler { function, id } => {
                write!(f, "CPS function {function} defines handler {id:?} twice")
            }
            CpsValidateError::MissingHandler { function, id } => {
                write!(
                    f,
                    "CPS function {function} references missing handler {id:?}"
                )
            }
            CpsValidateError::ContinuationArityMismatch {
                function,
                id,
                expected,
                actual,
            } => write!(
                f,
                "CPS function {function} calls continuation {id:?} with {actual} arguments, expected {expected}"
            ),
            CpsValidateError::MissingValue { function, id } => {
                write!(f, "CPS function {function} references missing value {id:?}")
            }
        }
    }
}

impl std::error::Error for CpsValidateError {}

pub fn validate_cps_module(module: &CpsModule) -> Result<(), CpsValidateError> {
    for function in module.functions.iter().chain(&module.roots) {
        validate_function(function)?;
    }
    Ok(())
}

fn validate_function(function: &CpsFunction) -> Result<(), CpsValidateError> {
    let mut continuation_ids = HashSet::new();
    for continuation in &function.continuations {
        if !continuation_ids.insert(continuation.id) {
            return Err(CpsValidateError::DuplicateContinuation {
                function: function.name.clone(),
                id: continuation.id,
            });
        }
    }
    if !continuation_ids.contains(&function.entry) {
        return Err(CpsValidateError::MissingEntry {
            function: function.name.clone(),
            entry: function.entry,
        });
    }

    let mut handler_ids = HashSet::new();
    for handler in &function.handlers {
        if !handler_ids.insert(handler.id) {
            return Err(CpsValidateError::DuplicateHandler {
                function: function.name.clone(),
                id: handler.id,
            });
        }
        require_continuation(function, &continuation_ids, handler.entry)?;
    }

    let defined_values = function_defined_values(function);
    for continuation in &function.continuations {
        validate_continuation(
            function,
            continuation,
            &continuation_ids,
            &handler_ids,
            &defined_values,
        )?;
    }
    Ok(())
}

fn function_defined_values(function: &CpsFunction) -> HashSet<CpsValueId> {
    let mut values = function.params.iter().copied().collect::<HashSet<_>>();
    for continuation in &function.continuations {
        values.extend(continuation.params.iter().copied());
        for stmt in &continuation.stmts {
            match stmt {
                CpsStmt::Literal { dest, .. }
                | CpsStmt::Primitive { dest, .. }
                | CpsStmt::DirectCall { dest, .. }
                | CpsStmt::CloneContinuation { dest, .. }
                | CpsStmt::Resume { dest, .. } => {
                    values.insert(*dest);
                }
            }
        }
    }
    values
}

fn validate_continuation(
    function: &CpsFunction,
    continuation: &CpsContinuation,
    continuation_ids: &HashSet<CpsContinuationId>,
    handler_ids: &HashSet<CpsHandlerId>,
    defined_values: &HashSet<CpsValueId>,
) -> Result<(), CpsValidateError> {
    let mut values = continuation.params.iter().copied().collect::<HashSet<_>>();
    for capture in &continuation.captures {
        require_value(function, defined_values, *capture)?;
        values.insert(*capture);
    }

    for stmt in &continuation.stmts {
        match stmt {
            CpsStmt::Literal { dest, .. } => {
                values.insert(*dest);
            }
            CpsStmt::Primitive { dest, args, .. } | CpsStmt::DirectCall { dest, args, .. } => {
                for arg in args {
                    require_value(function, &values, *arg)?;
                }
                values.insert(*dest);
            }
            CpsStmt::CloneContinuation { dest, source } => {
                require_value(function, &values, *source)?;
                values.insert(*dest);
            }
            CpsStmt::Resume {
                dest,
                resumption,
                arg,
            } => {
                require_value(function, &values, *resumption)?;
                require_value(function, &values, *arg)?;
                values.insert(*dest);
            }
        }
    }

    match &continuation.terminator {
        CpsTerminator::Return(value) => require_value(function, &values, *value),
        CpsTerminator::Continue { target, args } => {
            let target_cont = function
                .continuations
                .iter()
                .find(|continuation| continuation.id == *target)
                .ok_or_else(|| CpsValidateError::MissingContinuation {
                    function: function.name.clone(),
                    id: *target,
                })?;
            if target_cont.params.len() != args.len() {
                return Err(CpsValidateError::ContinuationArityMismatch {
                    function: function.name.clone(),
                    id: *target,
                    expected: target_cont.params.len(),
                    actual: args.len(),
                });
            }
            for arg in args {
                require_value(function, &values, *arg)?;
            }
            Ok(())
        }
        CpsTerminator::Branch {
            cond,
            then_cont,
            else_cont,
        } => {
            require_value(function, &values, *cond)?;
            require_continuation(function, continuation_ids, *then_cont)?;
            require_continuation(function, continuation_ids, *else_cont)
        }
        CpsTerminator::Perform {
            payload,
            resume,
            handler,
            ..
        } => {
            require_value(function, &values, *payload)?;
            require_continuation(function, continuation_ids, *resume)?;
            require_handler(function, handler_ids, *handler)
        }
    }
}

fn require_value(
    function: &CpsFunction,
    values: &HashSet<CpsValueId>,
    id: CpsValueId,
) -> Result<(), CpsValidateError> {
    if values.contains(&id) {
        Ok(())
    } else {
        Err(CpsValidateError::MissingValue {
            function: function.name.clone(),
            id,
        })
    }
}

fn require_continuation(
    function: &CpsFunction,
    continuation_ids: &HashSet<CpsContinuationId>,
    id: CpsContinuationId,
) -> Result<(), CpsValidateError> {
    if continuation_ids.contains(&id) {
        Ok(())
    } else {
        Err(CpsValidateError::MissingContinuation {
            function: function.name.clone(),
            id,
        })
    }
}

fn require_handler(
    function: &CpsFunction,
    handler_ids: &HashSet<CpsHandlerId>,
    id: CpsHandlerId,
) -> Result<(), CpsValidateError> {
    if handler_ids.contains(&id) {
        Ok(())
    } else {
        Err(CpsValidateError::MissingHandler {
            function: function.name.clone(),
            id,
        })
    }
}
