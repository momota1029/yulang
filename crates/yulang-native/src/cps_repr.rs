use std::collections::{BTreeMap, HashMap};
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
    ThunkPtr,
    ResumptionPtr,
    OpaqueI64,
    Conflict,
    Unknown,
}

impl CpsReprAbiLane {
    fn merge(self, other: Self) -> Self {
        match (self, other) {
            (left, right) if left == right => left,
            (Self::Unknown, known) | (known, Self::Unknown) => known,
            (Self::Conflict, _) | (_, Self::Conflict) => Self::Conflict,
            (Self::NativeFloat, _) | (_, Self::NativeFloat) => Self::Conflict,
            (Self::OpaqueI64, _) | (_, Self::OpaqueI64) => Self::OpaqueI64,
            _ => Self::OpaqueI64,
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
    pub arms: Vec<CpsReprHandlerArm>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CpsReprHandlerArm {
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
    ExpectedGuard {
        function: String,
        id: CpsValueId,
        value: runtime::VmValue,
    },
    MissingGuard {
        function: String,
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
    ExpectedRecord {
        function: String,
        value: runtime::VmValue,
    },
    MissingRecordField {
        function: String,
        field: core_ir::Name,
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
            CpsReprEvalError::ExpectedGuard {
                function,
                id,
                value,
            } => write!(
                f,
                "CPS repr function {function} expected guard value {id:?}, got {value:?}"
            ),
            CpsReprEvalError::MissingGuard { function } => {
                write!(f, "CPS repr function {function} has no active guard id")
            }
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
            CpsReprEvalError::ExpectedRecord { function, value } => write!(
                f,
                "CPS repr function {function} expected record value, got {value:?}"
            ),
            CpsReprEvalError::MissingRecordField { function, field } => write!(
                f,
                "CPS repr function {function} selected missing record field {field:?}"
            ),
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

fn propagate_direct_call_argument_lanes(
    module: &CpsReprModule,
    analysis: &mut CpsReprAbiAnalysis,
) -> bool {
    let function_params = module
        .functions
        .iter()
        .chain(&module.roots)
        .map(|function| (function.name.as_str(), function.params.as_slice()))
        .collect::<HashMap<_, _>>();
    let mut changed = false;
    for function in module.functions.iter().chain(&module.roots) {
        for continuation in &function.continuations {
            for stmt in &continuation.stmts {
                let CpsStmt::DirectCall { target, args, .. } = stmt else {
                    continue;
                };
                let Some(params) = function_params.get(target.as_str()).copied() else {
                    continue;
                };
                for (param, arg) in params.iter().zip(args) {
                    let lane = analysis
                        .value_lane(&function.name, *arg)
                        .unwrap_or(CpsReprAbiLane::Unknown);
                    if let Some(target_analysis) = analysis.functions.get_mut(target) {
                        changed |= merge_abi_lane(&mut target_analysis.values, *param, lane);
                    }
                }
            }
        }
    }
    changed
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
        changed |= propagate_direct_call_argument_lanes(module, &mut analysis);
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
                arms: handler
                    .arms
                    .iter()
                    .map(|arm| CpsReprHandlerArm {
                        effect: arm.effect.clone(),
                        entry: arm.entry,
                    })
                    .collect(),
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

fn make_thunk_entries(function: &CpsReprFunction) -> HashMap<CpsValueId, CpsContinuationId> {
    let mut entries = HashMap::new();
    for continuation in &function.continuations {
        for stmt in &continuation.stmts {
            if let CpsStmt::MakeThunk { dest, entry } = stmt {
                entries.insert(*dest, *entry);
            }
        }
    }
    entries
}

fn analyze_function_abi_lanes(
    function: &CpsReprFunction,
    module_analysis: &CpsReprAbiAnalysis,
) -> CpsReprFunctionAbiAnalysis {
    let mut values = HashMap::new();
    let mut continuation_returns = HashMap::new();
    let thunk_entries = make_thunk_entries(function);
    for param in &function.params {
        values.insert(
            *param,
            module_analysis
                .value_lane(&function.name, *param)
                .unwrap_or(CpsReprAbiLane::Unknown),
        );
    }
    for handler in &function.handlers {
        for arm in &handler.arms {
            if let Some(entry) = continuation_by_id_opt(function, arm.entry) {
                if let Some(payload) = entry.params.first() {
                    values.insert(*payload, CpsReprAbiLane::Unknown);
                }
                if let Some(resumption) = entry.params.get(1) {
                    values.insert(*resumption, CpsReprAbiLane::ResumptionPtr);
                }
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
                    CpsStmt::FreshGuard { .. }
                    | CpsStmt::PeekGuard { .. }
                    | CpsStmt::FindGuard { .. } => CpsReprAbiLane::ScalarI64,
                    CpsStmt::MakeThunk { .. } => CpsReprAbiLane::ThunkPtr,
                    CpsStmt::MakeClosure { .. } | CpsStmt::MakeRecursiveClosure { .. } => {
                        CpsReprAbiLane::ThunkPtr
                    }
                    CpsStmt::Tuple { .. }
                    | CpsStmt::Record { .. }
                    | CpsStmt::Variant { .. }
                    | CpsStmt::Select { .. } => CpsReprAbiLane::RuntimeValuePtr,
                    CpsStmt::TupleGet { .. } | CpsStmt::VariantPayload { .. } => {
                        CpsReprAbiLane::Unknown
                    }
                    CpsStmt::VariantTagEq { .. } => CpsReprAbiLane::ScalarI64,
                    CpsStmt::Primitive { op, .. } => primitive_result_lane(*op),
                    CpsStmt::DirectCall { target, .. } => module_analysis
                        .function_return_lane(target)
                        .unwrap_or(CpsReprAbiLane::Unknown),
                    CpsStmt::ApplyClosure { .. } => CpsReprAbiLane::Unknown,
                    CpsStmt::CloneContinuation { source, .. } => abi_lane(&values, *source),
                    CpsStmt::ForceThunk { thunk, .. } => thunk_entries
                        .get(thunk)
                        .and_then(|entry| continuation_returns.get(entry).copied())
                        .unwrap_or(CpsReprAbiLane::OpaqueI64),
                    CpsStmt::Resume { resumption, .. }
                    | CpsStmt::ResumeWithHandler { resumption, .. } => {
                        resumption_target_return_lane(
                            function,
                            &values,
                            &continuation_returns,
                            *resumption,
                        )
                    }
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
            effect,
            payload,
            resume,
            handler,
            blocked,
        } => {
            let mut changed = false;
            if let Some(blocked) = blocked {
                changed |= merge_abi_lane(values, *blocked, CpsReprAbiLane::ScalarI64);
            }
            if let Some(arm) = handler_arm_for_effect(function, *handler, effect)
                && let Some(entry) = continuation_by_id_opt(function, arm.entry)
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
    let thunk_entries = make_thunk_entries(function);
    for param in &function.params {
        values.insert(*param, CpsReprValueKind::Plain);
    }
    for handler in &function.handlers {
        for arm in &handler.arms {
            if let Some(entry) = function
                .continuations
                .iter()
                .find(|continuation| continuation.id == arm.entry)
            {
                if let Some(payload) = entry.params.first() {
                    values.insert(*payload, CpsReprValueKind::Plain);
                }
                if let Some(resumption) = entry.params.get(1) {
                    values.insert(*resumption, CpsReprValueKind::Resumption);
                }
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
                    | CpsStmt::FreshGuard { .. }
                    | CpsStmt::PeekGuard { .. }
                    | CpsStmt::FindGuard { .. }
                    | CpsStmt::MakeThunk { .. }
                    | CpsStmt::MakeClosure { .. }
                    | CpsStmt::MakeRecursiveClosure { .. }
                    | CpsStmt::Tuple { .. }
                    | CpsStmt::Record { .. }
                    | CpsStmt::Variant { .. }
                    | CpsStmt::Select { .. }
                    | CpsStmt::TupleGet { .. }
                    | CpsStmt::VariantTagEq { .. }
                    | CpsStmt::VariantPayload { .. }
                    | CpsStmt::Primitive { .. }
                    | CpsStmt::DirectCall { .. }
                    | CpsStmt::ApplyClosure { .. } => CpsReprValueKind::Plain,
                    CpsStmt::ForceThunk { thunk, .. } => thunk_entries
                        .get(thunk)
                        .and_then(|entry| continuation_returns.get(entry).copied())
                        .unwrap_or(CpsReprValueKind::Plain),
                    CpsStmt::CloneContinuation { source, .. } => value_kind(&values, *source),
                    CpsStmt::Resume { .. } | CpsStmt::ResumeWithHandler { .. } => {
                        CpsReprValueKind::Plain
                    }
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
                CpsTerminator::Perform {
                    effect, handler, ..
                } => handler_arm_for_effect(function, *handler, effect)
                    .and_then(|arm| continuation_returns.get(&arm.entry))
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
        CpsTerminator::Perform {
            effect, handler, ..
        } => handler_arm_for_effect(function, *handler, effect)
            .and_then(|arm| continuation_returns.get(&arm.entry))
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
        .flat_map(|handler| handler.arms.iter().map(move |arm| (handler.id, arm)))
        .filter(|(_, arm)| {
            continuation_by_id_opt(function, arm.entry).and_then(|entry| entry.params.get(1))
                == Some(&resumption)
        })
        .filter_map(|(handler_id, arm)| {
            function
                .continuations
                .iter()
                .filter_map(|continuation| match continuation.terminator {
                    CpsTerminator::Perform {
                        handler: used,
                        ref effect,
                        resume,
                        ..
                    } if used == handler_id && effect_matches(&arm.effect, effect) => {
                        continuation_returns.get(&resume).copied()
                    }
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

fn handler_arm_for_effect<'a>(
    function: &'a CpsReprFunction,
    id: CpsHandlerId,
    effect: &core_ir::Path,
) -> Option<&'a CpsReprHandlerArm> {
    function
        .handlers
        .iter()
        .find(|handler| handler.id == id)?
        .arms
        .iter()
        .find(|arm| effect_matches(&arm.effect, effect))
}

fn handler_arm_for_stack<'a>(
    function: &'a CpsReprFunction,
    stack: &[CpsReprHandlerFrame],
    effect: &core_ir::Path,
    blocked: Option<u64>,
) -> CpsReprEvalResult<(&'a CpsReprHandlerArm, Vec<CpsReprHandlerFrame>)> {
    for (index, frame) in stack.iter().enumerate().rev() {
        if blocked.is_some_and(|blocked| frame.guard_stack.iter().any(|entry| entry.id == blocked))
        {
            continue;
        }
        if let Some(arm) = handler_arm_for_effect(function, frame.handler, effect) {
            return Ok((arm, stack[..index].to_vec()));
        }
    }
    Err(CpsReprEvalError::MissingHandler {
        function: function.name.clone(),
        id: stack.last().expect("handler stack is non-empty").handler,
    })
}

fn handler_stack_with_static(
    active_handlers: &[CpsReprHandlerFrame],
    fallback: CpsHandlerId,
    guard_stack: &[CpsReprGuardEntry],
) -> Vec<CpsReprHandlerFrame> {
    if active_handlers.is_empty() {
        vec![CpsReprHandlerFrame {
            handler: fallback,
            guard_stack: guard_stack.to_vec(),
        }]
    } else {
        active_handlers.to_vec()
    }
}

fn handler_stack_with_pushed(
    active_handlers: &[CpsReprHandlerFrame],
    handler: CpsHandlerId,
    guard_stack: &[CpsReprGuardEntry],
) -> Vec<CpsReprHandlerFrame> {
    let mut stack = active_handlers.to_vec();
    stack.push(CpsReprHandlerFrame {
        handler,
        guard_stack: guard_stack.to_vec(),
    });
    stack
}

fn effect_matches(expected: &core_ir::Path, actual: &core_ir::Path) -> bool {
    actual == expected
        || (!expected.segments.is_empty()
            && actual.segments.len() == expected.segments.len() + 1
            && actual.segments.starts_with(&expected.segments))
        || (expected.segments.len() == 1 && actual.segments.last() == expected.segments.first())
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
        | CpsStmt::FreshGuard { dest, .. }
        | CpsStmt::PeekGuard { dest }
        | CpsStmt::FindGuard { dest, .. }
        | CpsStmt::MakeThunk { dest, .. }
        | CpsStmt::MakeClosure { dest, .. }
        | CpsStmt::MakeRecursiveClosure { dest, .. }
        | CpsStmt::ForceThunk { dest, .. }
        | CpsStmt::Tuple { dest, .. }
        | CpsStmt::Record { dest, .. }
        | CpsStmt::Variant { dest, .. }
        | CpsStmt::Select { dest, .. }
        | CpsStmt::TupleGet { dest, .. }
        | CpsStmt::VariantTagEq { dest, .. }
        | CpsStmt::VariantPayload { dest, .. }
        | CpsStmt::Primitive { dest, .. }
        | CpsStmt::DirectCall { dest, .. }
        | CpsStmt::ApplyClosure { dest, .. }
        | CpsStmt::CloneContinuation { dest, .. }
        | CpsStmt::Resume { dest, .. }
        | CpsStmt::ResumeWithHandler { dest, .. } => *dest,
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
    eval_continuations(
        module,
        function,
        function.entry,
        args.into_iter().map(CpsReprRuntimeValue::Plain).collect(),
        HashMap::new(),
        Vec::new(),
        Vec::new(),
    )
    .and_then(|value| into_plain_value(function, CpsValueId(usize::MAX), value))
}

fn eval_continuations(
    module: &CpsReprModule,
    function: &CpsReprFunction,
    entry: CpsContinuationId,
    mut args: Vec<CpsReprRuntimeValue>,
    mut values: HashMap<CpsValueId, CpsReprRuntimeValue>,
    active_handlers: Vec<CpsReprHandlerFrame>,
    guard_stack: Vec<CpsReprGuardEntry>,
) -> CpsReprEvalResult<CpsReprRuntimeValue> {
    let mut current = entry;
    let mut guard_stack = guard_stack;
    let mut next_guard_id = guard_stack
        .iter()
        .map(|entry| entry.id)
        .max()
        .map_or(0, |id| id + 1);
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
                CpsStmt::FreshGuard { dest, var } => {
                    let id = next_guard_id;
                    next_guard_id += 1;
                    guard_stack.push(CpsReprGuardEntry { var: *var, id });
                    values.insert(
                        *dest,
                        CpsReprRuntimeValue::Plain(runtime::VmValue::EffectId(id)),
                    );
                }
                CpsStmt::PeekGuard { dest } => {
                    let id = guard_stack.last().map(|entry| entry.id).ok_or_else(|| {
                        CpsReprEvalError::MissingGuard {
                            function: function.name.clone(),
                        }
                    })?;
                    values.insert(
                        *dest,
                        CpsReprRuntimeValue::Plain(runtime::VmValue::EffectId(id)),
                    );
                }
                CpsStmt::FindGuard { dest, guard } => {
                    let guard = read_effect_id(function, &values, *guard)?;
                    values.insert(
                        *dest,
                        CpsReprRuntimeValue::Plain(runtime::VmValue::Bool(
                            guard_stack.iter().any(|entry| entry.id == guard),
                        )),
                    );
                }
                CpsStmt::MakeThunk { dest, entry } => {
                    values.insert(
                        *dest,
                        CpsReprRuntimeValue::Thunk(CpsReprThunk {
                            entry: *entry,
                            values: values.clone(),
                            handlers: active_handlers.clone(),
                            guard_stack: guard_stack.clone(),
                        }),
                    );
                }
                CpsStmt::MakeClosure { dest, entry } => {
                    values.insert(
                        *dest,
                        CpsReprRuntimeValue::Closure(CpsReprClosure {
                            entry: *entry,
                            values: values.clone(),
                        }),
                    );
                }
                CpsStmt::MakeRecursiveClosure { dest, entry } => {
                    let mut closure_values = values.clone();
                    closure_values
                        .insert(*dest, CpsReprRuntimeValue::Plain(runtime::VmValue::Unit));
                    let closure = CpsReprRuntimeValue::Closure(CpsReprClosure {
                        entry: *entry,
                        values: closure_values.clone(),
                    });
                    closure_values.insert(*dest, closure.clone());
                    values.insert(*dest, closure);
                }
                CpsStmt::ForceThunk { dest, thunk } => {
                    let result = match read_value(function, &values, *thunk)? {
                        CpsReprRuntimeValue::Thunk(thunk) => eval_continuations(
                            module,
                            function,
                            thunk.entry,
                            Vec::new(),
                            thunk.values,
                            thunk.handlers,
                            thunk.guard_stack,
                        )?,
                        value => value,
                    };
                    values.insert(*dest, result);
                }
                CpsStmt::Tuple { dest, items } => {
                    let items = items
                        .iter()
                        .map(|id| read_plain_value(function, &values, *id))
                        .collect::<CpsReprEvalResult<Vec<_>>>()?;
                    values.insert(
                        *dest,
                        CpsReprRuntimeValue::Plain(runtime::VmValue::Tuple(items)),
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
                    values.insert(
                        *dest,
                        CpsReprRuntimeValue::Plain(runtime::VmValue::Record(record)),
                    );
                }
                CpsStmt::Variant { dest, tag, value } => {
                    let value = value
                        .map(|id| read_plain_value(function, &values, id))
                        .transpose()?
                        .map(Box::new);
                    values.insert(
                        *dest,
                        CpsReprRuntimeValue::Plain(runtime::VmValue::Variant {
                            tag: tag.clone(),
                            value,
                        }),
                    );
                }
                CpsStmt::Select { dest, base, field } => {
                    let value = match read_plain_value(function, &values, *base)? {
                        runtime::VmValue::Record(fields) => {
                            fields.get(field).cloned().ok_or_else(|| {
                                CpsReprEvalError::MissingRecordField {
                                    function: function.name.clone(),
                                    field: field.clone(),
                                }
                            })?
                        }
                        value => {
                            return Err(CpsReprEvalError::ExpectedRecord {
                                function: function.name.clone(),
                                value,
                            });
                        }
                    };
                    values.insert(*dest, CpsReprRuntimeValue::Plain(value));
                }
                CpsStmt::TupleGet { dest, tuple, index } => {
                    let value = match read_plain_value(function, &values, *tuple)? {
                        runtime::VmValue::Tuple(items) => {
                            items.get(*index).cloned().ok_or_else(|| {
                                CpsReprEvalError::MissingRecordField {
                                    function: function.name.clone(),
                                    field: core_ir::Name(index.to_string()),
                                }
                            })?
                        }
                        value => value,
                    };
                    values.insert(*dest, CpsReprRuntimeValue::Plain(value));
                }
                CpsStmt::VariantTagEq { dest, variant, tag } => {
                    let matches = matches!(
                        read_plain_value(function, &values, *variant)?,
                        runtime::VmValue::Variant { tag: actual, .. } if actual == *tag
                    );
                    values.insert(
                        *dest,
                        CpsReprRuntimeValue::Plain(runtime::VmValue::Bool(matches)),
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
                    values.insert(*dest, CpsReprRuntimeValue::Plain(value));
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
                CpsStmt::ApplyClosure { dest, closure, arg } => {
                    let closure = read_closure(function, &values, *closure)?;
                    let arg = read_plain_value(function, &values, *arg)?;
                    let result = eval_continuations(
                        module,
                        function,
                        closure.entry,
                        vec![CpsReprRuntimeValue::Plain(arg)],
                        closure.values,
                        active_handlers.clone(),
                        guard_stack.clone(),
                    )?;
                    values.insert(*dest, result);
                }
                CpsStmt::CloneContinuation { dest, source } => {
                    let value = read_value(function, &values, *source)?;
                    values.insert(*dest, value);
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
                        resumption.handlers.clone(),
                        resumption.guard_stack.clone(),
                    )?;
                    values.insert(*dest, result);
                }
                CpsStmt::ResumeWithHandler {
                    dest,
                    resumption,
                    arg,
                    handler,
                    envs: _,
                } => {
                    let resumption = read_resumption(function, &values, *resumption)?;
                    let arg = read_plain_value(function, &values, *arg)?;
                    let result = eval_continuations(
                        module,
                        function,
                        resumption.target,
                        vec![CpsReprRuntimeValue::Plain(arg)],
                        resumption.values.clone(),
                        handler_stack_with_pushed(&resumption.handlers, *handler, &guard_stack),
                        resumption.guard_stack.clone(),
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
                let (handler, handler_body_stack) =
                    handler_arm_for_stack(function, &handler_stack, effect, blocked)?;
                let resumption = CpsReprRuntimeValue::Resumption(CpsReprResumption {
                    target: *resume,
                    values: values.clone(),
                    handlers: handler_stack,
                    guard_stack: guard_stack.clone(),
                });
                return eval_continuations(
                    module,
                    function,
                    handler.entry,
                    vec![CpsReprRuntimeValue::Plain(payload), resumption],
                    values,
                    handler_body_stack,
                    guard_stack,
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

fn read_effect_id(
    function: &CpsReprFunction,
    values: &HashMap<CpsValueId, CpsReprRuntimeValue>,
    id: CpsValueId,
) -> CpsReprEvalResult<u64> {
    match read_plain_value(function, values, id)? {
        runtime::VmValue::EffectId(value_id) => Ok(value_id),
        value => Err(CpsReprEvalError::ExpectedGuard {
            function: function.name.clone(),
            id,
            value,
        }),
    }
}

fn read_resumption(
    function: &CpsReprFunction,
    values: &HashMap<CpsValueId, CpsReprRuntimeValue>,
    id: CpsValueId,
) -> CpsReprEvalResult<CpsReprResumption> {
    match read_value(function, values, id)? {
        CpsReprRuntimeValue::Plain(_)
        | CpsReprRuntimeValue::Thunk(_)
        | CpsReprRuntimeValue::Closure(_) => Err(CpsReprEvalError::ExpectedResumption {
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
        CpsReprRuntimeValue::Resumption(_)
        | CpsReprRuntimeValue::Thunk(_)
        | CpsReprRuntimeValue::Closure(_) => Err(CpsReprEvalError::ExpectedPlainValue {
            function: function.name.clone(),
            id,
        }),
    }
}

fn read_closure(
    function: &CpsReprFunction,
    values: &HashMap<CpsValueId, CpsReprRuntimeValue>,
    id: CpsValueId,
) -> CpsReprEvalResult<CpsReprClosure> {
    match read_value(function, values, id)? {
        CpsReprRuntimeValue::Closure(closure) => Ok(closure),
        CpsReprRuntimeValue::Plain(_)
        | CpsReprRuntimeValue::Resumption(_)
        | CpsReprRuntimeValue::Thunk(_) => Err(CpsReprEvalError::ExpectedPlainValue {
            function: function.name.clone(),
            id,
        }),
    }
}

#[derive(Debug, Clone, PartialEq)]
enum CpsReprRuntimeValue {
    Plain(runtime::VmValue),
    Resumption(CpsReprResumption),
    Thunk(CpsReprThunk),
    Closure(CpsReprClosure),
}

#[derive(Debug, Clone, PartialEq)]
struct CpsReprResumption {
    target: CpsContinuationId,
    values: HashMap<CpsValueId, CpsReprRuntimeValue>,
    handlers: Vec<CpsReprHandlerFrame>,
    guard_stack: Vec<CpsReprGuardEntry>,
}

#[derive(Debug, Clone, PartialEq)]
struct CpsReprThunk {
    entry: CpsContinuationId,
    values: HashMap<CpsValueId, CpsReprRuntimeValue>,
    handlers: Vec<CpsReprHandlerFrame>,
    guard_stack: Vec<CpsReprGuardEntry>,
}

#[derive(Debug, Clone, PartialEq)]
struct CpsReprClosure {
    entry: CpsContinuationId,
    values: HashMap<CpsValueId, CpsReprRuntimeValue>,
}

#[derive(Debug, Clone, PartialEq)]
struct CpsReprHandlerFrame {
    handler: CpsHandlerId,
    guard_stack: Vec<CpsReprGuardEntry>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct CpsReprGuardEntry {
    var: runtime::EffectIdVar,
    id: u64,
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
    fn evaluates_resumption_under_fresh_handler_stack() {
        let module = rebased_resumption_module();
        let lowered = lower_cps_repr_module(&module);

        assert_eq!(
            eval_cps_repr_module(&lowered).expect("evaluated"),
            vec![runtime::VmValue::Int("13".to_string())]
        );
    }

    #[test]
    fn skips_handler_frame_blocked_by_guard_snapshot() {
        let module = blocked_handler_snapshot_module();
        let lowered = lower_cps_repr_module(&module);

        assert_eq!(
            eval_cps_repr_module(&lowered).expect("evaluated"),
            vec![runtime::VmValue::Int("100".to_string())]
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
            analysis.value_kind("root", CpsValueId(10)),
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
                    arms: vec![crate::cps_ir::CpsHandlerArm {
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
                            CpsStmt::CloneContinuation {
                                dest: CpsValueId(10),
                                source: CpsValueId(5),
                            },
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
                                resumption: CpsValueId(10),
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

    fn rebased_resumption_module() -> CpsModule {
        let effect = core_ir::Path::from_name(core_ir::Name("choose".to_string()));
        CpsModule {
            functions: Vec::new(),
            roots: vec![CpsFunction {
                name: "root".to_string(),
                params: Vec::new(),
                entry: CpsContinuationId(0),
                handlers: vec![
                    crate::cps_ir::CpsHandler {
                        id: CpsHandlerId(0),
                        arms: vec![crate::cps_ir::CpsHandlerArm {
                            effect: effect.clone(),
                            entry: CpsContinuationId(2),
                        }],
                    },
                    crate::cps_ir::CpsHandler {
                        id: CpsHandlerId(1),
                        arms: vec![crate::cps_ir::CpsHandlerArm {
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

    fn blocked_handler_snapshot_module() -> CpsModule {
        let start = core_ir::Path::from_name(core_ir::Name("start".to_string()));
        let choose = core_ir::Path::from_name(core_ir::Name("choose".to_string()));
        CpsModule {
            functions: Vec::new(),
            roots: vec![CpsFunction {
                name: "root".to_string(),
                params: Vec::new(),
                entry: CpsContinuationId(0),
                handlers: vec![
                    crate::cps_ir::CpsHandler {
                        id: CpsHandlerId(0),
                        arms: vec![
                            crate::cps_ir::CpsHandlerArm {
                                effect: start.clone(),
                                entry: CpsContinuationId(2),
                            },
                            crate::cps_ir::CpsHandlerArm {
                                effect: choose.clone(),
                                entry: CpsContinuationId(5),
                            },
                        ],
                    },
                    crate::cps_ir::CpsHandler {
                        id: CpsHandlerId(1),
                        arms: vec![crate::cps_ir::CpsHandlerArm {
                            effect: choose.clone(),
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
                            effect: start,
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
                            literal: CpsLiteral::Int("0".to_string()),
                        }],
                        terminator: CpsTerminator::Perform {
                            effect: choose.clone(),
                            payload: CpsValueId(2),
                            resume: CpsContinuationId(3),
                            handler: CpsHandlerId(0),
                            blocked: Some(CpsValueId(1)),
                        },
                    },
                    CpsContinuation {
                        id: CpsContinuationId(2),
                        params: vec![CpsValueId(3), CpsValueId(4)],
                        captures: Vec::new(),
                        shot_kind: CpsShotKind::MultiShot,
                        stmts: vec![
                            CpsStmt::FreshGuard {
                                dest: CpsValueId(5),
                                var: yulang_runtime::EffectIdVar(0),
                            },
                            CpsStmt::ResumeWithHandler {
                                dest: CpsValueId(6),
                                resumption: CpsValueId(4),
                                arg: CpsValueId(5),
                                handler: CpsHandlerId(1),
                                envs: Vec::new(),
                            },
                        ],
                        terminator: CpsTerminator::Return(CpsValueId(6)),
                    },
                    CpsContinuation {
                        id: CpsContinuationId(3),
                        params: vec![CpsValueId(7)],
                        captures: Vec::new(),
                        shot_kind: CpsShotKind::MultiShot,
                        stmts: Vec::new(),
                        terminator: CpsTerminator::Return(CpsValueId(7)),
                    },
                    CpsContinuation {
                        id: CpsContinuationId(4),
                        params: vec![CpsValueId(8), CpsValueId(9)],
                        captures: Vec::new(),
                        shot_kind: CpsShotKind::MultiShot,
                        stmts: vec![CpsStmt::Literal {
                            dest: CpsValueId(10),
                            literal: CpsLiteral::Int("200".to_string()),
                        }],
                        terminator: CpsTerminator::Return(CpsValueId(10)),
                    },
                    CpsContinuation {
                        id: CpsContinuationId(5),
                        params: vec![CpsValueId(11), CpsValueId(12)],
                        captures: Vec::new(),
                        shot_kind: CpsShotKind::MultiShot,
                        stmts: vec![CpsStmt::Literal {
                            dest: CpsValueId(13),
                            literal: CpsLiteral::Int("100".to_string()),
                        }],
                        terminator: CpsTerminator::Return(CpsValueId(13)),
                    },
                ],
            }],
        }
    }
}
