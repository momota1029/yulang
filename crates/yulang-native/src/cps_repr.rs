use std::collections::HashMap;
use std::fmt;

use yulang_core_ir as core_ir;
use yulang_runtime as runtime;

use crate::cps_ir::{
    CpsContinuation, CpsContinuationId, CpsFunction, CpsHandlerId, CpsLiteral, CpsModule,
    CpsShotKind, CpsStmt, CpsTerminator, CpsValueId,
};

pub type CpsReprEvalResult<T> = Result<T, CpsReprEvalError>;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CpsReprValueKind {
    Plain,
    Resumption,
    Unknown,
}

impl CpsReprValueKind {
    fn merge(self, other: Self) -> Self {
        match (self, other) {
            (left, right) if left == right => left,
            (Self::Unknown, known) | (known, Self::Unknown) => known,
            _ => Self::Unknown,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CpsReprValueAnalysis {
    pub functions: HashMap<String, CpsReprFunctionValueAnalysis>,
}

impl CpsReprValueAnalysis {
    pub fn value_kind(&self, function: &str, value: CpsValueId) -> Option<CpsReprValueKind> {
        self.functions.get(function)?.values.get(&value).copied()
    }

    pub fn continuation_return_kind(
        &self,
        function: &str,
        continuation: CpsContinuationId,
    ) -> Option<CpsReprValueKind> {
        self.functions
            .get(function)?
            .continuation_returns
            .get(&continuation)
            .copied()
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CpsReprFunctionValueAnalysis {
    pub values: HashMap<CpsValueId, CpsReprValueKind>,
    pub continuation_returns: HashMap<CpsContinuationId, CpsReprValueKind>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CpsReprAbiLane {
    ScalarI64,
    NativeFloat,
    RuntimeValuePtr,
    ResumptionPtr,
    Unknown,
}

impl CpsReprAbiLane {
    fn merge(self, other: Self) -> Self {
        match (self, other) {
            (left, right) if left == right => left,
            (Self::Unknown, known) | (known, Self::Unknown) => known,
            _ => Self::Unknown,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CpsReprAbiAnalysis {
    pub functions: HashMap<String, CpsReprFunctionAbiAnalysis>,
}

impl CpsReprAbiAnalysis {
    pub fn function_return_lane(&self, function: &str) -> Option<CpsReprAbiLane> {
        let function = self.functions.get(function)?;
        function.continuation_returns.get(&function.entry).copied()
    }

    pub fn value_lane(&self, function: &str, value: CpsValueId) -> Option<CpsReprAbiLane> {
        self.functions.get(function)?.values.get(&value).copied()
    }

    pub fn continuation_return_lane(
        &self,
        function: &str,
        continuation: CpsContinuationId,
    ) -> Option<CpsReprAbiLane> {
        self.functions
            .get(function)?
            .continuation_returns
            .get(&continuation)
            .copied()
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CpsReprFunctionAbiAnalysis {
    pub entry: CpsContinuationId,
    pub values: HashMap<CpsValueId, CpsReprAbiLane>,
    pub continuation_returns: HashMap<CpsContinuationId, CpsReprAbiLane>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CpsReprModule {
    pub functions: Vec<CpsReprFunction>,
    pub roots: Vec<CpsReprFunction>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CpsReprFunction {
    pub name: String,
    pub params: Vec<CpsValueId>,
    pub entry: CpsContinuationId,
    pub continuations: Vec<CpsReprContinuation>,
    pub handlers: Vec<CpsReprHandler>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CpsReprContinuation {
    pub id: CpsContinuationId,
    pub params: Vec<CpsValueId>,
    pub environment: Vec<CpsReprEnvironmentSlot>,
    pub shot_kind: CpsShotKind,
    pub stmts: Vec<CpsStmt>,
    pub terminator: CpsTerminator,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct CpsReprEnvironmentSlot {
    pub index: usize,
    pub value: CpsValueId,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CpsReprHandler {
    pub id: CpsHandlerId,
    pub effect: core_ir::Path,
    pub entry: CpsContinuationId,
}

#[derive(Debug, Clone, PartialEq)]
pub enum CpsReprEvalError {
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
    UnsupportedStmt {
        function: String,
        kind: &'static str,
    },
    UnsupportedPrimitive {
        op: core_ir::PrimitiveOp,
    },
    PrimitiveTypeMismatch {
        op: core_ir::PrimitiveOp,
        value: runtime::VmValue,
    },
}

impl fmt::Display for CpsReprEvalError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            CpsReprEvalError::MissingFunction { name } => {
                write!(f, "CPS repr function {name} is missing")
            }
            CpsReprEvalError::MissingContinuation { function, id } => {
                write!(
                    f,
                    "CPS repr function {function} is missing continuation {id:?}"
                )
            }
            CpsReprEvalError::MissingHandler { function, id } => {
                write!(f, "CPS repr function {function} is missing handler {id:?}")
            }
            CpsReprEvalError::ContinuationArgumentMismatch {
                function,
                id,
                expected,
                actual,
            } => write!(
                f,
                "CPS repr continuation {function}::{id:?} expected {expected} arguments, got {actual}"
            ),
            CpsReprEvalError::FunctionArgumentMismatch {
                function,
                expected,
                actual,
            } => write!(
                f,
                "CPS repr function {function} expected {expected} arguments, got {actual}"
            ),
            CpsReprEvalError::MissingValue { function, id } => {
                write!(
                    f,
                    "CPS repr function {function} references missing value {id:?}"
                )
            }
            CpsReprEvalError::ExpectedPlainValue { function, id } => write!(
                f,
                "CPS repr function {function} expected plain value {id:?}"
            ),
            CpsReprEvalError::ExpectedResumption { function, id } => write!(
                f,
                "CPS repr function {function} expected resumption value {id:?}"
            ),
            CpsReprEvalError::UnsupportedStmt { function, kind } => write!(
                f,
                "CPS repr evaluator does not support {kind} statements in `{function}` yet"
            ),
            CpsReprEvalError::UnsupportedPrimitive { op } => {
                write!(
                    f,
                    "CPS repr evaluator does not support primitive {op:?} yet"
                )
            }
            CpsReprEvalError::PrimitiveTypeMismatch { op, value } => {
                write!(f, "CPS repr primitive {op:?} cannot accept value {value:?}")
            }
        }
    }
}

impl std::error::Error for CpsReprEvalError {}

pub fn lower_cps_repr_module(module: &CpsModule) -> CpsReprModule {
    CpsReprModule {
        functions: module.functions.iter().map(lower_function).collect(),
        roots: module.roots.iter().map(lower_function).collect(),
    }
}

pub fn eval_cps_repr_module(module: &CpsReprModule) -> CpsReprEvalResult<Vec<runtime::VmValue>> {
    module
        .roots
        .iter()
        .map(|root| eval_function(module, root, Vec::new()))
        .collect()
}

pub fn analyze_cps_repr_values(module: &CpsReprModule) -> CpsReprValueAnalysis {
    CpsReprValueAnalysis {
        functions: module
            .functions
            .iter()
            .chain(&module.roots)
            .map(|function| (function.name.clone(), analyze_function_values(function)))
            .collect(),
    }
}

pub fn analyze_cps_repr_abi_lanes(module: &CpsReprModule) -> CpsReprAbiAnalysis {
    let mut analysis = CpsReprAbiAnalysis {
        functions: module
            .functions
            .iter()
            .chain(&module.roots)
            .map(|function| {
                (
                    function.name.clone(),
                    CpsReprFunctionAbiAnalysis {
                        entry: function.entry,
                        values: HashMap::new(),
                        continuation_returns: HashMap::new(),
                    },
                )
            })
            .collect(),
    };
    loop {
        let mut changed = false;
        for function in module.functions.iter().chain(&module.roots) {
            let function_analysis = analyze_function_abi_lanes(function, &analysis);
            if analysis.functions.get(&function.name) != Some(&function_analysis) {
                analysis
                    .functions
                    .insert(function.name.clone(), function_analysis);
                changed = true;
            }
        }
        if !changed {
            return analysis;
        }
    }
}

fn lower_function(function: &CpsFunction) -> CpsReprFunction {
    CpsReprFunction {
        name: function.name.clone(),
        params: function.params.clone(),
        entry: function.entry,
        continuations: function
            .continuations
            .iter()
            .map(lower_continuation)
            .collect(),
        handlers: function
            .handlers
            .iter()
            .map(|handler| CpsReprHandler {
                id: handler.id,
                effect: handler.effect.clone(),
                entry: handler.entry,
            })
            .collect(),
    }
}

fn lower_continuation(continuation: &CpsContinuation) -> CpsReprContinuation {
    CpsReprContinuation {
        id: continuation.id,
        params: continuation.params.clone(),
        environment: continuation
            .captures
            .iter()
            .copied()
            .enumerate()
            .map(|(index, value)| CpsReprEnvironmentSlot { index, value })
            .collect(),
        shot_kind: continuation.shot_kind,
        stmts: continuation.stmts.clone(),
        terminator: continuation.terminator.clone(),
    }
}

fn analyze_function_abi_lanes(
    function: &CpsReprFunction,
    module_analysis: &CpsReprAbiAnalysis,
) -> CpsReprFunctionAbiAnalysis {
    let mut values = HashMap::new();
    let mut continuation_returns = HashMap::new();
    for param in &function.params {
        values.insert(*param, CpsReprAbiLane::Unknown);
    }
    for handler in &function.handlers {
        if let Some(entry) = continuation_by_id_opt(function, handler.entry) {
            if let Some(payload) = entry.params.first() {
                values.insert(*payload, CpsReprAbiLane::Unknown);
            }
            if let Some(resumption) = entry.params.get(1) {
                values.insert(*resumption, CpsReprAbiLane::ResumptionPtr);
            }
        }
    }

    loop {
        let mut changed = false;
        for continuation in &function.continuations {
            for param in &continuation.params {
                values.entry(*param).or_insert(CpsReprAbiLane::Unknown);
            }
            for slot in &continuation.environment {
                values.entry(slot.value).or_insert(CpsReprAbiLane::Unknown);
            }
            for stmt in &continuation.stmts {
                let lane = match stmt {
                    CpsStmt::Literal { literal, .. } => literal_lane(literal),
                    CpsStmt::Primitive { op, .. } => primitive_result_lane(*op),
                    CpsStmt::DirectCall { target, .. } => module_analysis
                        .function_return_lane(target)
                        .unwrap_or(CpsReprAbiLane::Unknown),
                    CpsStmt::CloneContinuation { source, .. } => abi_lane(&values, *source),
                    CpsStmt::Resume { resumption, .. } => resumption_target_return_lane(
                        function,
                        &values,
                        &continuation_returns,
                        *resumption,
                    ),
                };
                if merge_abi_lane(&mut values, stmt_dest(stmt), lane) {
                    changed = true;
                }
            }
            if propagate_terminator_argument_lanes(function, &mut values, &continuation.terminator)
            {
                changed = true;
            }
            let return_lane =
                terminator_return_lane(function, &values, &continuation_returns, continuation);
            if continuation_returns.get(&continuation.id) != Some(&return_lane) {
                continuation_returns.insert(continuation.id, return_lane);
                changed = true;
            }
        }
        if !changed {
            return CpsReprFunctionAbiAnalysis {
                entry: function.entry,
                values,
                continuation_returns,
            };
        }
    }
}

fn propagate_terminator_argument_lanes(
    function: &CpsReprFunction,
    values: &mut HashMap<CpsValueId, CpsReprAbiLane>,
    terminator: &CpsTerminator,
) -> bool {
    match terminator {
        CpsTerminator::Continue { target, args } => {
            let Some(target) = continuation_by_id_opt(function, *target) else {
                return false;
            };
            merge_param_lanes(values, &target.params, args)
        }
        CpsTerminator::Perform {
            payload,
            resume,
            handler,
            ..
        } => {
            let mut changed = false;
            if let Some(handler) = function.handlers.iter().find(|entry| entry.id == *handler)
                && let Some(entry) = continuation_by_id_opt(function, handler.entry)
                && let Some(param) = entry.params.first()
            {
                let lane = abi_lane(values, *payload);
                changed |= merge_abi_lane(values, *param, lane);
            }
            if let Some(resume) = continuation_by_id_opt(function, *resume)
                && let Some(param) = resume.params.first()
            {
                changed |= merge_abi_lane(values, *param, abi_lane(values, *payload));
            }
            changed
        }
        CpsTerminator::Return(_) | CpsTerminator::Branch { .. } => false,
    }
}

fn merge_param_lanes(
    values: &mut HashMap<CpsValueId, CpsReprAbiLane>,
    params: &[CpsValueId],
    args: &[CpsValueId],
) -> bool {
    let mut changed = false;
    for (param, arg) in params.iter().zip(args) {
        changed |= merge_abi_lane(values, *param, abi_lane(values, *arg));
    }
    changed
}

fn analyze_function_values(function: &CpsReprFunction) -> CpsReprFunctionValueAnalysis {
    let mut values = HashMap::new();
    let mut continuation_returns = HashMap::new();
    for param in &function.params {
        values.insert(*param, CpsReprValueKind::Plain);
    }
    for handler in &function.handlers {
        if let Some(entry) = function
            .continuations
            .iter()
            .find(|continuation| continuation.id == handler.entry)
        {
            if let Some(payload) = entry.params.first() {
                values.insert(*payload, CpsReprValueKind::Plain);
            }
            if let Some(resumption) = entry.params.get(1) {
                values.insert(*resumption, CpsReprValueKind::Resumption);
            }
        }
    }

    loop {
        let mut changed = false;
        for continuation in &function.continuations {
            for param in &continuation.params {
                values.entry(*param).or_insert(CpsReprValueKind::Unknown);
            }
            for slot in &continuation.environment {
                values
                    .entry(slot.value)
                    .or_insert(CpsReprValueKind::Unknown);
            }
            for stmt in &continuation.stmts {
                let kind = match stmt {
                    CpsStmt::Literal { .. }
                    | CpsStmt::Primitive { .. }
                    | CpsStmt::DirectCall { .. } => CpsReprValueKind::Plain,
                    CpsStmt::CloneContinuation { source, .. } => value_kind(&values, *source),
                    CpsStmt::Resume { .. } => CpsReprValueKind::Plain,
                };
                if merge_value_kind(&mut values, stmt_dest(stmt), kind) {
                    changed = true;
                }
            }
            let return_kind = match &continuation.terminator {
                CpsTerminator::Return(value) => value_kind(&values, *value),
                CpsTerminator::Continue { target, .. } => continuation_returns
                    .get(target)
                    .copied()
                    .unwrap_or(CpsReprValueKind::Unknown),
                CpsTerminator::Branch {
                    then_cont,
                    else_cont,
                    ..
                } => continuation_returns
                    .get(then_cont)
                    .copied()
                    .unwrap_or(CpsReprValueKind::Unknown)
                    .merge(
                        continuation_returns
                            .get(else_cont)
                            .copied()
                            .unwrap_or(CpsReprValueKind::Unknown),
                    ),
                CpsTerminator::Perform { handler, .. } => function
                    .handlers
                    .iter()
                    .find(|entry| entry.id == *handler)
                    .and_then(|entry| continuation_returns.get(&entry.entry))
                    .copied()
                    .unwrap_or(CpsReprValueKind::Unknown),
            };
            if continuation_returns.get(&continuation.id) != Some(&return_kind) {
                continuation_returns.insert(continuation.id, return_kind);
                changed = true;
            }
        }
        if !changed {
            return CpsReprFunctionValueAnalysis {
                values,
                continuation_returns,
            };
        }
    }
}

fn literal_lane(literal: &CpsLiteral) -> CpsReprAbiLane {
    match literal {
        CpsLiteral::Int(_) | CpsLiteral::Bool(_) | CpsLiteral::Unit => CpsReprAbiLane::ScalarI64,
        CpsLiteral::Float(_) => CpsReprAbiLane::NativeFloat,
        CpsLiteral::String(_) => CpsReprAbiLane::RuntimeValuePtr,
    }
}

fn primitive_result_lane(op: core_ir::PrimitiveOp) -> CpsReprAbiLane {
    use core_ir::PrimitiveOp;
    match op {
        PrimitiveOp::BoolNot
        | PrimitiveOp::BoolEq
        | PrimitiveOp::IntEq
        | PrimitiveOp::IntLt
        | PrimitiveOp::IntLe
        | PrimitiveOp::IntGt
        | PrimitiveOp::IntGe
        | PrimitiveOp::IntAdd
        | PrimitiveOp::IntSub
        | PrimitiveOp::IntMul
        | PrimitiveOp::IntDiv
        | PrimitiveOp::ListLen
        | PrimitiveOp::StringLen => CpsReprAbiLane::ScalarI64,
        PrimitiveOp::FloatEq
        | PrimitiveOp::FloatLt
        | PrimitiveOp::FloatLe
        | PrimitiveOp::FloatGt
        | PrimitiveOp::FloatGe => CpsReprAbiLane::ScalarI64,
        PrimitiveOp::FloatAdd
        | PrimitiveOp::FloatSub
        | PrimitiveOp::FloatMul
        | PrimitiveOp::FloatDiv => CpsReprAbiLane::NativeFloat,
        PrimitiveOp::ListEmpty
        | PrimitiveOp::ListSingleton
        | PrimitiveOp::ListMerge
        | PrimitiveOp::ListIndexRange
        | PrimitiveOp::ListSplice
        | PrimitiveOp::ListIndexRangeRaw
        | PrimitiveOp::ListSpliceRaw
        | PrimitiveOp::ListViewRaw
        | PrimitiveOp::StringIndex
        | PrimitiveOp::StringIndexRange
        | PrimitiveOp::StringSplice
        | PrimitiveOp::StringIndexRangeRaw
        | PrimitiveOp::StringSpliceRaw
        | PrimitiveOp::StringConcat
        | PrimitiveOp::IntToString
        | PrimitiveOp::IntToHex
        | PrimitiveOp::IntToUpperHex
        | PrimitiveOp::FloatToString
        | PrimitiveOp::BoolToString => CpsReprAbiLane::RuntimeValuePtr,
        PrimitiveOp::ListIndex => CpsReprAbiLane::Unknown,
    }
}

fn terminator_return_lane(
    function: &CpsReprFunction,
    values: &HashMap<CpsValueId, CpsReprAbiLane>,
    continuation_returns: &HashMap<CpsContinuationId, CpsReprAbiLane>,
    continuation: &CpsReprContinuation,
) -> CpsReprAbiLane {
    match &continuation.terminator {
        CpsTerminator::Return(value) => abi_lane(values, *value),
        CpsTerminator::Continue { target, .. } => continuation_returns
            .get(target)
            .copied()
            .unwrap_or(CpsReprAbiLane::Unknown),
        CpsTerminator::Branch {
            then_cont,
            else_cont,
            ..
        } => continuation_returns
            .get(then_cont)
            .copied()
            .unwrap_or(CpsReprAbiLane::Unknown)
            .merge(
                continuation_returns
                    .get(else_cont)
                    .copied()
                    .unwrap_or(CpsReprAbiLane::Unknown),
            ),
        CpsTerminator::Perform { handler, .. } => function
            .handlers
            .iter()
            .find(|entry| entry.id == *handler)
            .and_then(|entry| continuation_returns.get(&entry.entry))
            .copied()
            .unwrap_or(CpsReprAbiLane::Unknown),
    }
}

fn resumption_target_return_lane(
    function: &CpsReprFunction,
    values: &HashMap<CpsValueId, CpsReprAbiLane>,
    continuation_returns: &HashMap<CpsContinuationId, CpsReprAbiLane>,
    resumption: CpsValueId,
) -> CpsReprAbiLane {
    if abi_lane(values, resumption) != CpsReprAbiLane::ResumptionPtr {
        return CpsReprAbiLane::Unknown;
    }
    function
        .handlers
        .iter()
        .filter(|handler| {
            continuation_by_id_opt(function, handler.entry).and_then(|entry| entry.params.get(1))
                == Some(&resumption)
        })
        .filter_map(|handler| {
            function
                .continuations
                .iter()
                .filter_map(|continuation| match continuation.terminator {
                    CpsTerminator::Perform {
                        handler: used,
                        resume,
                        ..
                    } if used == handler.id => continuation_returns.get(&resume).copied(),
                    _ => None,
                })
                .fold(None, |current, lane| {
                    Some(current.map_or(lane, |current: CpsReprAbiLane| current.merge(lane)))
                })
        })
        .fold(None, |current, lane| {
            Some(current.map_or(lane, |current: CpsReprAbiLane| current.merge(lane)))
        })
        .unwrap_or(CpsReprAbiLane::Unknown)
}

fn abi_lane(values: &HashMap<CpsValueId, CpsReprAbiLane>, value: CpsValueId) -> CpsReprAbiLane {
    values
        .get(&value)
        .copied()
        .unwrap_or(CpsReprAbiLane::Unknown)
}

fn merge_abi_lane(
    values: &mut HashMap<CpsValueId, CpsReprAbiLane>,
    value: CpsValueId,
    lane: CpsReprAbiLane,
) -> bool {
    let merged = values
        .get(&value)
        .copied()
        .map(|current| current.merge(lane))
        .unwrap_or(lane);
    if values.get(&value) == Some(&merged) {
        false
    } else {
        values.insert(value, merged);
        true
    }
}

fn stmt_dest(stmt: &CpsStmt) -> CpsValueId {
    match stmt {
        CpsStmt::Literal { dest, .. }
        | CpsStmt::Primitive { dest, .. }
        | CpsStmt::DirectCall { dest, .. }
        | CpsStmt::CloneContinuation { dest, .. }
        | CpsStmt::Resume { dest, .. } => *dest,
    }
}

fn value_kind(
    values: &HashMap<CpsValueId, CpsReprValueKind>,
    value: CpsValueId,
) -> CpsReprValueKind {
    values
        .get(&value)
        .copied()
        .unwrap_or(CpsReprValueKind::Unknown)
}

fn merge_value_kind(
    values: &mut HashMap<CpsValueId, CpsReprValueKind>,
    value: CpsValueId,
    kind: CpsReprValueKind,
) -> bool {
    let merged = values
        .get(&value)
        .copied()
        .map(|current| current.merge(kind))
        .unwrap_or(kind);
    if values.get(&value) == Some(&merged) {
        false
    } else {
        values.insert(value, merged);
        true
    }
}

fn eval_function(
    module: &CpsReprModule,
    function: &CpsReprFunction,
    args: Vec<runtime::VmValue>,
) -> CpsReprEvalResult<runtime::VmValue> {
    if function.params.len() != args.len() {
        return Err(CpsReprEvalError::FunctionArgumentMismatch {
            function: function.name.clone(),
            expected: function.params.len(),
            actual: args.len(),
        });
    }
    let mut values = HashMap::new();
    for (param, value) in function.params.iter().copied().zip(args) {
        values.insert(param, CpsReprRuntimeValue::Plain(value));
    }
    eval_continuations(module, function, function.entry, Vec::new(), values)
        .and_then(|value| into_plain_value(function, CpsValueId(usize::MAX), value))
}

fn eval_continuations(
    module: &CpsReprModule,
    function: &CpsReprFunction,
    entry: CpsContinuationId,
    mut args: Vec<CpsReprRuntimeValue>,
    mut values: HashMap<CpsValueId, CpsReprRuntimeValue>,
) -> CpsReprEvalResult<CpsReprRuntimeValue> {
    let mut current = entry;
    loop {
        let continuation = continuation_by_id(function, current)?;
        if continuation.params.len() != args.len() {
            return Err(CpsReprEvalError::ContinuationArgumentMismatch {
                function: function.name.clone(),
                id: continuation.id,
                expected: continuation.params.len(),
                actual: args.len(),
            });
        }
        for (param, value) in continuation.params.iter().copied().zip(args) {
            values.insert(param, value);
        }
        args = Vec::new();

        for stmt in &continuation.stmts {
            match stmt {
                CpsStmt::Literal { dest, literal } => {
                    values.insert(*dest, CpsReprRuntimeValue::Plain(eval_literal(literal)));
                }
                CpsStmt::Primitive { dest, op, args } => {
                    let args = args
                        .iter()
                        .map(|id| read_plain_value(function, &values, *id))
                        .collect::<CpsReprEvalResult<Vec<_>>>()?;
                    values.insert(
                        *dest,
                        CpsReprRuntimeValue::Plain(eval_primitive(*op, &args)?),
                    );
                }
                CpsStmt::DirectCall { dest, target, args } => {
                    let target_function = module
                        .functions
                        .iter()
                        .find(|function| &function.name == target)
                        .ok_or_else(|| CpsReprEvalError::MissingFunction {
                            name: target.clone(),
                        })?;
                    let args = args
                        .iter()
                        .map(|id| read_plain_value(function, &values, *id))
                        .collect::<CpsReprEvalResult<Vec<_>>>()?;
                    values.insert(
                        *dest,
                        CpsReprRuntimeValue::Plain(eval_function(module, target_function, args)?),
                    );
                }
                CpsStmt::CloneContinuation { .. } => {
                    return Err(CpsReprEvalError::UnsupportedStmt {
                        function: function.name.clone(),
                        kind: "clone continuation",
                    });
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
                        vec![CpsReprRuntimeValue::Plain(arg)],
                        resumption.values.clone(),
                    )?;
                    values.insert(*dest, result);
                }
            }
        }

        match &continuation.terminator {
            CpsTerminator::Return(value) => return read_value(function, &values, *value),
            CpsTerminator::Continue { target, args: next } => {
                args = next
                    .iter()
                    .map(|id| read_value(function, &values, *id))
                    .collect::<CpsReprEvalResult<Vec<_>>>()?;
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
                payload,
                resume,
                handler,
                ..
            } => {
                let payload = read_plain_value(function, &values, *payload)?;
                let handler = handler_by_id(function, *handler)?;
                let resumption = CpsReprRuntimeValue::Resumption(CpsReprResumption {
                    target: *resume,
                    values: values.clone(),
                });
                return eval_continuations(
                    module,
                    function,
                    handler.entry,
                    vec![CpsReprRuntimeValue::Plain(payload), resumption],
                    values,
                );
            }
        }
    }
}

fn continuation_by_id(
    function: &CpsReprFunction,
    id: CpsContinuationId,
) -> CpsReprEvalResult<&CpsReprContinuation> {
    function
        .continuations
        .iter()
        .find(|continuation| continuation.id == id)
        .ok_or_else(|| CpsReprEvalError::MissingContinuation {
            function: function.name.clone(),
            id,
        })
}

fn continuation_by_id_opt(
    function: &CpsReprFunction,
    id: CpsContinuationId,
) -> Option<&CpsReprContinuation> {
    function
        .continuations
        .iter()
        .find(|continuation| continuation.id == id)
}

fn handler_by_id(
    function: &CpsReprFunction,
    id: CpsHandlerId,
) -> CpsReprEvalResult<&CpsReprHandler> {
    function
        .handlers
        .iter()
        .find(|handler| handler.id == id)
        .ok_or_else(|| CpsReprEvalError::MissingHandler {
            function: function.name.clone(),
            id,
        })
}

fn read_value(
    function: &CpsReprFunction,
    values: &HashMap<CpsValueId, CpsReprRuntimeValue>,
    id: CpsValueId,
) -> CpsReprEvalResult<CpsReprRuntimeValue> {
    values
        .get(&id)
        .cloned()
        .ok_or_else(|| CpsReprEvalError::MissingValue {
            function: function.name.clone(),
            id,
        })
}

fn read_plain_value(
    function: &CpsReprFunction,
    values: &HashMap<CpsValueId, CpsReprRuntimeValue>,
    id: CpsValueId,
) -> CpsReprEvalResult<runtime::VmValue> {
    into_plain_value(function, id, read_value(function, values, id)?)
}

fn read_resumption(
    function: &CpsReprFunction,
    values: &HashMap<CpsValueId, CpsReprRuntimeValue>,
    id: CpsValueId,
) -> CpsReprEvalResult<CpsReprResumption> {
    match read_value(function, values, id)? {
        CpsReprRuntimeValue::Plain(_) => Err(CpsReprEvalError::ExpectedResumption {
            function: function.name.clone(),
            id,
        }),
        CpsReprRuntimeValue::Resumption(resumption) => Ok(resumption),
    }
}

fn into_plain_value(
    function: &CpsReprFunction,
    id: CpsValueId,
    value: CpsReprRuntimeValue,
) -> CpsReprEvalResult<runtime::VmValue> {
    match value {
        CpsReprRuntimeValue::Plain(value) => Ok(value),
        CpsReprRuntimeValue::Resumption(_) => Err(CpsReprEvalError::ExpectedPlainValue {
            function: function.name.clone(),
            id,
        }),
    }
}

#[derive(Debug, Clone, PartialEq)]
enum CpsReprRuntimeValue {
    Plain(runtime::VmValue),
    Resumption(CpsReprResumption),
}

#[derive(Debug, Clone, PartialEq)]
struct CpsReprResumption {
    target: CpsContinuationId,
    values: HashMap<CpsValueId, CpsReprRuntimeValue>,
}

fn eval_literal(literal: &CpsLiteral) -> runtime::VmValue {
    match literal {
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
) -> CpsReprEvalResult<runtime::VmValue> {
    use core_ir::PrimitiveOp;
    match op {
        PrimitiveOp::BoolNot => Ok(runtime::VmValue::Bool(!bool_value(op, &args[0])?)),
        PrimitiveOp::IntAdd => Ok(runtime::VmValue::Int(
            (int_value(op, &args[0])? + int_value(op, &args[1])?).to_string(),
        )),
        PrimitiveOp::IntSub => Ok(runtime::VmValue::Int(
            (int_value(op, &args[0])? - int_value(op, &args[1])?).to_string(),
        )),
        PrimitiveOp::IntMul => Ok(runtime::VmValue::Int(
            (int_value(op, &args[0])? * int_value(op, &args[1])?).to_string(),
        )),
        PrimitiveOp::IntEq => Ok(runtime::VmValue::Bool(
            int_value(op, &args[0])? == int_value(op, &args[1])?,
        )),
        PrimitiveOp::IntLt => Ok(runtime::VmValue::Bool(
            int_value(op, &args[0])? < int_value(op, &args[1])?,
        )),
        PrimitiveOp::IntLe => Ok(runtime::VmValue::Bool(
            int_value(op, &args[0])? <= int_value(op, &args[1])?,
        )),
        _ => Err(CpsReprEvalError::UnsupportedPrimitive { op }),
    }
}

fn int_value(op: core_ir::PrimitiveOp, value: &runtime::VmValue) -> CpsReprEvalResult<i64> {
    match value {
        runtime::VmValue::Int(value) => {
            value
                .parse()
                .map_err(|_| CpsReprEvalError::PrimitiveTypeMismatch {
                    op,
                    value: runtime::VmValue::Int(value.clone()),
                })
        }
        value => Err(CpsReprEvalError::PrimitiveTypeMismatch {
            op,
            value: value.clone(),
        }),
    }
}

fn bool_value(op: core_ir::PrimitiveOp, value: &runtime::VmValue) -> CpsReprEvalResult<bool> {
    match value {
        runtime::VmValue::Bool(value) => Ok(*value),
        value => Err(CpsReprEvalError::PrimitiveTypeMismatch {
            op,
            value: value.clone(),
        }),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn lowers_continuations_to_code_with_environment_slots() {
        let module = CpsModule {
            functions: Vec::new(),
            roots: vec![CpsFunction {
                name: "root".to_string(),
                params: Vec::new(),
                entry: CpsContinuationId(0),
                handlers: Vec::new(),
                continuations: vec![CpsContinuation {
                    id: CpsContinuationId(0),
                    params: vec![CpsValueId(0)],
                    captures: vec![CpsValueId(2), CpsValueId(1)],
                    shot_kind: CpsShotKind::MultiShot,
                    stmts: Vec::new(),
                    terminator: CpsTerminator::Return(CpsValueId(0)),
                }],
            }],
        };

        let lowered = lower_cps_repr_module(&module);

        assert_eq!(
            lowered.roots[0].continuations[0].environment,
            vec![
                CpsReprEnvironmentSlot {
                    index: 0,
                    value: CpsValueId(2),
                },
                CpsReprEnvironmentSlot {
                    index: 1,
                    value: CpsValueId(1),
                },
            ]
        );
    }

    #[test]
    fn evaluates_pure_continuation_flow() {
        let module = CpsModule {
            functions: Vec::new(),
            roots: vec![CpsFunction {
                name: "root".to_string(),
                params: Vec::new(),
                entry: CpsContinuationId(0),
                handlers: Vec::new(),
                continuations: vec![
                    CpsContinuation {
                        id: CpsContinuationId(0),
                        params: Vec::new(),
                        captures: Vec::new(),
                        shot_kind: CpsShotKind::OneShot,
                        stmts: vec![
                            CpsStmt::Literal {
                                dest: CpsValueId(0),
                                literal: CpsLiteral::Int("40".to_string()),
                            },
                            CpsStmt::Literal {
                                dest: CpsValueId(1),
                                literal: CpsLiteral::Int("2".to_string()),
                            },
                            CpsStmt::Primitive {
                                dest: CpsValueId(2),
                                op: core_ir::PrimitiveOp::IntAdd,
                                args: vec![CpsValueId(0), CpsValueId(1)],
                            },
                        ],
                        terminator: CpsTerminator::Continue {
                            target: CpsContinuationId(1),
                            args: vec![CpsValueId(2)],
                        },
                    },
                    CpsContinuation {
                        id: CpsContinuationId(1),
                        params: vec![CpsValueId(3)],
                        captures: Vec::new(),
                        shot_kind: CpsShotKind::OneShot,
                        stmts: Vec::new(),
                        terminator: CpsTerminator::Return(CpsValueId(3)),
                    },
                ],
            }],
        };
        let lowered = lower_cps_repr_module(&module);

        assert_eq!(
            eval_cps_repr_module(&lowered).expect("evaluated"),
            vec![runtime::VmValue::Int("42".to_string())]
        );
    }

    #[test]
    fn evaluates_multishot_resumption_flow() {
        let module = multishot_resumption_module();
        let lowered = lower_cps_repr_module(&module);

        assert_eq!(
            eval_cps_repr_module(&lowered).expect("evaluated"),
            vec![runtime::VmValue::Int("23".to_string())]
        );
    }

    #[test]
    fn analyzes_resumption_value_kind() {
        let lowered = lower_cps_repr_module(&multishot_resumption_module());
        let analysis = analyze_cps_repr_values(&lowered);

        assert_eq!(
            analysis.value_kind("root", CpsValueId(4)),
            Some(CpsReprValueKind::Plain)
        );
        assert_eq!(
            analysis.value_kind("root", CpsValueId(5)),
            Some(CpsReprValueKind::Resumption)
        );
        assert_eq!(
            analysis.value_kind("root", CpsValueId(7)),
            Some(CpsReprValueKind::Plain)
        );
        assert_eq!(
            analysis.continuation_return_kind("root", CpsContinuationId(2)),
            Some(CpsReprValueKind::Plain)
        );
    }

    #[test]
    fn analyzes_resumption_abi_lane() {
        let lowered = lower_cps_repr_module(&multishot_resumption_module());
        let analysis = analyze_cps_repr_abi_lanes(&lowered);

        assert_eq!(
            analysis.value_lane("root", CpsValueId(5)),
            Some(CpsReprAbiLane::ResumptionPtr)
        );
        assert_eq!(
            analysis.value_lane("root", CpsValueId(7)),
            Some(CpsReprAbiLane::ScalarI64)
        );
        assert_eq!(
            analysis.continuation_return_lane("root", CpsContinuationId(2)),
            Some(CpsReprAbiLane::ScalarI64)
        );
        assert_eq!(
            analysis.function_return_lane("root"),
            Some(CpsReprAbiLane::ScalarI64)
        );
    }

    #[test]
    fn propagates_direct_call_abi_lane() {
        let module = CpsModule {
            functions: vec![CpsFunction {
                name: "make_int".to_string(),
                params: Vec::new(),
                entry: CpsContinuationId(0),
                handlers: Vec::new(),
                continuations: vec![CpsContinuation {
                    id: CpsContinuationId(0),
                    params: Vec::new(),
                    captures: Vec::new(),
                    shot_kind: CpsShotKind::OneShot,
                    stmts: vec![CpsStmt::Literal {
                        dest: CpsValueId(0),
                        literal: CpsLiteral::Int("42".to_string()),
                    }],
                    terminator: CpsTerminator::Return(CpsValueId(0)),
                }],
            }],
            roots: vec![CpsFunction {
                name: "root".to_string(),
                params: Vec::new(),
                entry: CpsContinuationId(0),
                handlers: Vec::new(),
                continuations: vec![CpsContinuation {
                    id: CpsContinuationId(0),
                    params: Vec::new(),
                    captures: Vec::new(),
                    shot_kind: CpsShotKind::OneShot,
                    stmts: vec![CpsStmt::DirectCall {
                        dest: CpsValueId(0),
                        target: "make_int".to_string(),
                        args: Vec::new(),
                    }],
                    terminator: CpsTerminator::Return(CpsValueId(0)),
                }],
            }],
        };
        let lowered = lower_cps_repr_module(&module);
        let analysis = analyze_cps_repr_abi_lanes(&lowered);

        assert_eq!(
            analysis.value_lane("root", CpsValueId(0)),
            Some(CpsReprAbiLane::ScalarI64)
        );
        assert_eq!(
            analysis.function_return_lane("root"),
            Some(CpsReprAbiLane::ScalarI64)
        );
    }

    fn multishot_resumption_module() -> CpsModule {
        let effect = core_ir::Path::from_name(core_ir::Name("choose".to_string()));
        CpsModule {
            functions: Vec::new(),
            roots: vec![CpsFunction {
                name: "root".to_string(),
                params: Vec::new(),
                entry: CpsContinuationId(0),
                handlers: vec![crate::cps_ir::CpsHandler {
                    id: CpsHandlerId(0),
                    effect: effect.clone(),
                    entry: CpsContinuationId(2),
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
        }
    }
}
