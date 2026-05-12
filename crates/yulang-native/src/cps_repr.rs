use std::collections::{BTreeMap, HashMap};
use std::fmt;
use std::rc::Rc;

use yulang_runtime as runtime;
use yulang_typed_ir as typed_ir;

use crate::cps_ir::{
    CpsContinuation, CpsContinuationId, CpsFunction, CpsHandlerEnv, CpsHandlerId, CpsLiteral,
    CpsModule, CpsShotKind, CpsStmt, CpsTerminator, CpsValueId,
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
    pub effect: typed_ir::Path,
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
            CpsReprEvalError::InvalidPrimitiveArity {
                op,
                expected,
                actual,
            } => write!(
                f,
                "CPS repr primitive {op:?} expected {expected} args, got {actual}"
            ),
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
        .map(|root| {
            let value = eval_function(module, root, Vec::new())?;
            let value = unwrap_aborted_repr(value);
            into_plain_value(root, CpsValueId(usize::MAX), value)
        })
        .collect()
}

fn unwrap_aborted_repr(value: CpsReprRuntimeValue) -> CpsReprRuntimeValue {
    match value {
        CpsReprRuntimeValue::Aborted(inner) => unwrap_aborted_repr(*inner),
        other => other,
    }
}

fn cps_repr_value_from_vm(value: runtime::VmValue) -> CpsReprRuntimeValue {
    match value {
        runtime::VmValue::Tuple(items) => {
            CpsReprRuntimeValue::Tuple(items.into_iter().map(cps_repr_value_from_vm).collect())
        }
        runtime::VmValue::Variant { tag, value } => CpsReprRuntimeValue::Variant {
            tag,
            value: value.map(|v| Box::new(cps_repr_value_from_vm(*v))),
        },
        runtime::VmValue::List(list) => {
            let items = list
                .to_vec()
                .into_iter()
                .map(|item| cps_repr_value_from_vm((*item).clone()))
                .collect::<Vec<_>>();
            CpsReprRuntimeValue::List(Rc::new(items))
        }
        other => CpsReprRuntimeValue::Plain(other),
    }
}

fn cps_repr_value_to_vm(value: CpsReprRuntimeValue) -> Option<runtime::VmValue> {
    match value {
        CpsReprRuntimeValue::Plain(value) => Some(value),
        CpsReprRuntimeValue::Aborted(inner) => cps_repr_value_to_vm(*inner),
        CpsReprRuntimeValue::Tuple(items) => Some(runtime::VmValue::Tuple(
            items
                .into_iter()
                .map(cps_repr_value_to_vm)
                .collect::<Option<Vec<_>>>()?,
        )),
        CpsReprRuntimeValue::Variant { tag, value } => Some(runtime::VmValue::Variant {
            tag,
            value: match value {
                Some(value) => Some(Box::new(cps_repr_value_to_vm(*value)?)),
                None => None,
            },
        }),
        CpsReprRuntimeValue::List(items) => {
            let vm_items = items
                .iter()
                .cloned()
                .map(cps_repr_value_to_vm)
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
        CpsReprRuntimeValue::Resumption(_)
        | CpsReprRuntimeValue::Thunk(_)
        | CpsReprRuntimeValue::Closure(_)
        // write26: ScopeReturn must be matched against an installed
        // handler before reaching root. If it does, that's a lowering
        // bug — surface as None so `into_plain_value` reports it.
        | CpsReprRuntimeValue::ScopeReturn { .. } => None,
    }
}

fn eval_cps_repr_primitive(
    op: typed_ir::PrimitiveOp,
    args: Vec<CpsReprRuntimeValue>,
) -> CpsReprEvalResult<CpsReprRuntimeValue> {
    use typed_ir::PrimitiveOp;
    match op {
        PrimitiveOp::ListEmpty => {
            if args.len() > 1 {
                return Err(CpsReprEvalError::InvalidPrimitiveArity {
                    op,
                    expected: 1,
                    actual: args.len(),
                });
            }
            Ok(CpsReprRuntimeValue::List(Rc::new(Vec::new())))
        }
        PrimitiveOp::ListSingleton => {
            if args.len() != 1 {
                return Err(CpsReprEvalError::InvalidPrimitiveArity {
                    op,
                    expected: 1,
                    actual: args.len(),
                });
            }
            Ok(CpsReprRuntimeValue::List(Rc::new(vec![
                args.into_iter().next().unwrap(),
            ])))
        }
        PrimitiveOp::ListMerge => {
            if args.len() != 2 {
                return Err(CpsReprEvalError::InvalidPrimitiveArity {
                    op,
                    expected: 2,
                    actual: args.len(),
                });
            }
            let mut iter = args.into_iter();
            let left = iter.next().unwrap();
            let right = iter.next().unwrap();
            let mut merged = control_repr_list_items(op, left)?;
            merged.extend(control_repr_list_items(op, right)?);
            Ok(CpsReprRuntimeValue::List(Rc::new(merged)))
        }
        PrimitiveOp::ListLen => {
            if args.len() != 1 {
                return Err(CpsReprEvalError::InvalidPrimitiveArity {
                    op,
                    expected: 1,
                    actual: args.len(),
                });
            }
            let items = control_repr_list_items(op, args.into_iter().next().unwrap())?;
            Ok(CpsReprRuntimeValue::Plain(runtime::VmValue::Int(
                items.len().to_string(),
            )))
        }
        PrimitiveOp::ListIndex => {
            if args.len() != 2 {
                return Err(CpsReprEvalError::InvalidPrimitiveArity {
                    op,
                    expected: 2,
                    actual: args.len(),
                });
            }
            let mut iter = args.into_iter();
            let list = iter.next().unwrap();
            let idx_val = iter.next().unwrap();
            let items = control_repr_list_items(op, list)?;
            let idx = cps_repr_value_to_usize(op, idx_val)?;
            items
                .into_iter()
                .nth(idx)
                .ok_or(CpsReprEvalError::UnsupportedPrimitive { op })
        }
        PrimitiveOp::ListIndexRangeRaw => {
            if args.len() != 3 {
                return Err(CpsReprEvalError::InvalidPrimitiveArity {
                    op,
                    expected: 3,
                    actual: args.len(),
                });
            }
            let mut iter = args.into_iter();
            let list = iter.next().unwrap();
            let start_val = iter.next().unwrap();
            let end_val = iter.next().unwrap();
            let items = control_repr_list_items(op, list)?;
            let start = cps_repr_value_to_usize(op, start_val)?;
            let end = cps_repr_value_to_usize(op, end_val)?;
            Ok(CpsReprRuntimeValue::List(Rc::new(
                items.into_iter().skip(start).take(end - start).collect(),
            )))
        }
        _ => {
            let plain_args = args
                .into_iter()
                .map(cps_repr_value_to_vm)
                .collect::<Option<Vec<_>>>()
                .ok_or(CpsReprEvalError::UnsupportedPrimitive { op })?;
            eval_primitive(op, &plain_args).map(cps_repr_value_from_vm)
        }
    }
}

fn cps_repr_value_to_usize(
    op: typed_ir::PrimitiveOp,
    value: CpsReprRuntimeValue,
) -> CpsReprEvalResult<usize> {
    match value {
        CpsReprRuntimeValue::Plain(runtime::VmValue::Int(s)) => s
            .parse::<usize>()
            .map_err(|_| CpsReprEvalError::UnsupportedPrimitive { op }),
        _ => Err(CpsReprEvalError::UnsupportedPrimitive { op }),
    }
}

fn control_repr_list_items(
    op: typed_ir::PrimitiveOp,
    value: CpsReprRuntimeValue,
) -> CpsReprEvalResult<Vec<CpsReprRuntimeValue>> {
    match value {
        CpsReprRuntimeValue::List(items) => Ok(items.as_ref().clone()),
        CpsReprRuntimeValue::Plain(plain) => match plain {
            runtime::VmValue::List(list) => Ok(list
                .to_vec()
                .into_iter()
                .map(|item| cps_repr_value_from_vm((*item).clone()))
                .collect()),
            other => Err(CpsReprEvalError::PrimitiveTypeMismatch { op, value: other }),
        },
        _ => Err(CpsReprEvalError::UnsupportedPrimitive { op }),
    }
}

fn function_by_name_repr<'a>(
    module: &'a CpsReprModule,
    name: &str,
) -> CpsReprEvalResult<&'a CpsReprFunction> {
    module
        .functions
        .iter()
        .chain(module.roots.iter())
        .find(|function| function.name == name)
        .ok_or_else(|| CpsReprEvalError::MissingFunction {
            name: name.to_string(),
        })
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
                    CpsStmt::InstallHandler { .. } | CpsStmt::UninstallHandler { .. } => continue,
                };
                if let Some(dest) = stmt_dest(stmt) {
                    if merge_abi_lane(&mut values, dest, lane) {
                        changed = true;
                    }
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
        CpsTerminator::EffectfulCall { args, resume, .. } => {
            // Propagate result lane to the resume continuation's parameter.
            if let Some(resume) = continuation_by_id_opt(function, *resume)
                && let Some(_param) = resume.params.first()
            {
                // Arg lanes flow through the call; result lane is unknown
                // statically, so just touch them to keep the fixpoint going.
                let _ = args;
            }
            false
        }
        CpsTerminator::EffectfulApply { resume, .. }
        | CpsTerminator::EffectfulForce { resume, .. } => {
            let _ = continuation_by_id_opt(function, *resume);
            false
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
                    CpsStmt::InstallHandler { .. } | CpsStmt::UninstallHandler { .. } => continue,
                };
                if let Some(dest) = stmt_dest(stmt) {
                    if merge_value_kind(&mut values, dest, kind) {
                        changed = true;
                    }
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
                CpsTerminator::EffectfulCall { resume, .. }
                | CpsTerminator::EffectfulApply { resume, .. }
                | CpsTerminator::EffectfulForce { resume, .. } => continuation_returns
                    .get(resume)
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

fn primitive_result_lane(op: typed_ir::PrimitiveOp) -> CpsReprAbiLane {
    use typed_ir::PrimitiveOp;
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
        | PrimitiveOp::FloatGe
        | PrimitiveOp::StringEq => CpsReprAbiLane::ScalarI64,
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
        CpsTerminator::EffectfulCall { resume, .. }
        | CpsTerminator::EffectfulApply { resume, .. }
        | CpsTerminator::EffectfulForce { resume, .. } => continuation_returns
            .get(resume)
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
    effect: &typed_ir::Path,
) -> Option<&'a CpsReprHandlerArm> {
    function
        .handlers
        .iter()
        .find(|handler| handler.id == id)?
        .arms
        .iter()
        .find(|arm| effect_matches(&arm.effect, effect))
}

fn handler_arm_for_effect_in_module<'a>(
    module: &'a CpsReprModule,
    id: CpsHandlerId,
    effect: &typed_ir::Path,
) -> Option<(&'a CpsReprHandlerArm, &'a CpsReprFunction)> {
    for owner in module.functions.iter().chain(module.roots.iter()) {
        if let Some(arm) = handler_arm_for_effect(owner, id, effect) {
            return Some((arm, owner));
        }
    }
    None
}

fn handler_arm_for_stack<'a>(
    module: &'a CpsReprModule,
    current_function: &'a CpsReprFunction,
    stack: &'a [CpsReprHandlerFrame],
    effect: &typed_ir::Path,
    blocked: Option<u64>,
) -> CpsReprEvalResult<(
    &'a CpsReprHandlerArm,
    &'a CpsReprHandlerFrame,
    Vec<CpsReprHandlerFrame>,
    &'a CpsReprFunction,
)> {
    for (index, frame) in stack.iter().enumerate().rev() {
        if blocked.is_some_and(|blocked| frame.guard_stack.iter().any(|entry| entry.id == blocked))
        {
            continue;
        }
        if let Some((arm, owner)) = handler_arm_for_effect_in_module(module, frame.handler, effect)
        {
            return Ok((arm, frame, stack[..index].to_vec(), owner));
        }
    }
    Err(CpsReprEvalError::MissingHandler {
        function: current_function.name.clone(),
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
            prompt: fresh_repr_prompt(),
            handler: fallback,
            guard_stack: guard_stack.to_vec(),
            envs: Vec::new(),
            escape: REPR_EXIT_RWH_TARGET,
            escape_owner_function: String::new(),
            return_frame_threshold: 0,
            inherited: false,
            install_eval_id: REPR_SYNTHETIC_EVAL_ID,
        }]
    } else {
        active_handlers.to_vec()
    }
}

fn handler_stack_with_pushed(
    active_handlers: &[CpsReprHandlerFrame],
    handler: CpsHandlerId,
    guard_stack: &[CpsReprGuardEntry],
    envs: Vec<CpsReprEvaluatedHandlerEnv>,
) -> Vec<CpsReprHandlerFrame> {
    let mut stack = active_handlers.to_vec();
    stack.push(CpsReprHandlerFrame {
        prompt: fresh_repr_prompt(),
        handler,
        guard_stack: guard_stack.to_vec(),
        envs,
        escape: REPR_EXIT_RWH_TARGET,
        escape_owner_function: String::new(),
        return_frame_threshold: 0,
        inherited: false,
        install_eval_id: REPR_SYNTHETIC_EVAL_ID,
    });
    stack
}

fn capture_handler_envs(
    function: &CpsReprFunction,
    values: &HashMap<CpsValueId, CpsReprRuntimeValue>,
    envs: &[CpsHandlerEnv],
) -> CpsReprEvalResult<Vec<CpsReprEvaluatedHandlerEnv>> {
    envs.iter()
        .map(|env| {
            let mut values_by_id = Vec::new();
            for value in &env.values {
                values_by_id.push((*value, read_value(function, values, *value)?));
            }
            Ok(CpsReprEvaluatedHandlerEnv {
                entry: env.entry,
                values: values_by_id,
            })
        })
        .collect()
}

fn values_with_handler_env(
    mut values: HashMap<CpsValueId, CpsReprRuntimeValue>,
    frame: &CpsReprHandlerFrame,
    entry: CpsContinuationId,
) -> HashMap<CpsValueId, CpsReprRuntimeValue> {
    let Some(env) = frame.envs.iter().find(|env| env.entry == entry) else {
        return values;
    };
    for (id, value) in &env.values {
        values.insert(*id, value.clone());
    }
    values
}

fn effect_matches(expected: &typed_ir::Path, actual: &typed_ir::Path) -> bool {
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

fn stmt_dest(stmt: &CpsStmt) -> Option<CpsValueId> {
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
        | CpsStmt::ResumeWithHandler { dest, .. } => Some(*dest),
        CpsStmt::InstallHandler { .. } | CpsStmt::UninstallHandler { .. } => None,
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
) -> CpsReprEvalResult<CpsReprRuntimeValue> {
    eval_function_with_context(
        module,
        function,
        args.into_iter().map(CpsReprRuntimeValue::Plain).collect(),
        Vec::new(),
        Vec::new(),
        Vec::new(),
        0,
    )
}

fn eval_function_with_context(
    module: &CpsReprModule,
    function: &CpsReprFunction,
    args: Vec<CpsReprRuntimeValue>,
    active_handlers: Vec<CpsReprHandlerFrame>,
    guard_stack: Vec<CpsReprGuardEntry>,
    return_frames: Vec<CpsReprReturnFrame>,
    initial_frame_count: usize,
) -> CpsReprEvalResult<CpsReprRuntimeValue> {
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
        args,
        HashMap::new(),
        active_handlers,
        guard_stack,
        return_frames,
        initial_frame_count,
    )
}

/// write26: entry point that issues a fresh `CpsReprEvalId`. Mirrors
/// `cps_eval::eval_continuations` (which calls `into_inherited` before
/// `resume_continuation`).
fn eval_continuations(
    module: &CpsReprModule,
    function: &CpsReprFunction,
    entry: CpsContinuationId,
    args: Vec<CpsReprRuntimeValue>,
    values: HashMap<CpsValueId, CpsReprRuntimeValue>,
    active_handlers: Vec<CpsReprHandlerFrame>,
    guard_stack: Vec<CpsReprGuardEntry>,
    return_frames: Vec<CpsReprReturnFrame>,
    initial_frame_count: usize,
) -> CpsReprEvalResult<CpsReprRuntimeValue> {
    let current_eval_id = fresh_repr_eval_id();
    resume_continuation(
        module,
        function,
        entry,
        args,
        values,
        into_inherited_repr(active_handlers),
        guard_stack,
        return_frames,
        initial_frame_count,
        current_eval_id,
    )
}

/// write26: mark every handler frame as inherited so a fresh eval frame
/// does not resolve a `ScopeReturn` against handlers whose install eval
/// lives in a parent eval. Mirrors `cps_eval::into_inherited`.
fn into_inherited_repr(mut handlers: Vec<CpsReprHandlerFrame>) -> Vec<CpsReprHandlerFrame> {
    for frame in &mut handlers {
        frame.inherited = true;
    }
    handlers
}

/// write26 port of `cps_eval::ScopeReturnAction`.
enum ScopeReturnActionRepr {
    Value(CpsReprRuntimeValue),
    JumpOrExit {
        target: CpsContinuationId,
        value: CpsReprRuntimeValue,
        return_frame_threshold: usize,
    },
    Propagate(CpsReprRuntimeValue),
}

/// write26 port of `cps_eval::handle_scope_return`.
fn handle_scope_return_repr(
    result: CpsReprRuntimeValue,
    active_handlers: &mut Vec<CpsReprHandlerFrame>,
    current_function: &str,
    current_eval_id: CpsReprEvalId,
) -> ScopeReturnActionRepr {
    match result {
        CpsReprRuntimeValue::ScopeReturn {
            prompt,
            target,
            value,
        } => {
            if let Some(index) = active_handlers.iter().rposition(|frame| {
                frame.prompt == prompt && frame.install_eval_id == current_eval_id
            }) {
                let frame = &active_handlers[index];
                let frame_owner_match = target == REPR_EXIT_RWH_TARGET
                    || frame.escape_owner_function == current_function;
                let threshold = frame.return_frame_threshold;
                if !frame_owner_match {
                    return ScopeReturnActionRepr::Propagate(CpsReprRuntimeValue::ScopeReturn {
                        prompt,
                        target,
                        value,
                    });
                }
                active_handlers.truncate(index);
                ScopeReturnActionRepr::JumpOrExit {
                    target,
                    value: *value,
                    return_frame_threshold: threshold,
                }
            } else {
                ScopeReturnActionRepr::Propagate(CpsReprRuntimeValue::ScopeReturn {
                    prompt,
                    target,
                    value,
                })
            }
        }
        other => ScopeReturnActionRepr::Value(other),
    }
}

/// write26: core eval loop. Does NOT call `into_inherited_repr` and does
/// NOT issue a fresh eval id — both responsibilities lie with the caller
/// (`eval_continuations` or `continue_return_frames_repr`).
fn resume_continuation(
    module: &CpsReprModule,
    function: &CpsReprFunction,
    entry: CpsContinuationId,
    mut args: Vec<CpsReprRuntimeValue>,
    mut values: HashMap<CpsValueId, CpsReprRuntimeValue>,
    active_handlers: Vec<CpsReprHandlerFrame>,
    guard_stack: Vec<CpsReprGuardEntry>,
    return_frames: Vec<CpsReprReturnFrame>,
    initial_frame_count: usize,
    current_eval_id: CpsReprEvalId,
) -> CpsReprEvalResult<CpsReprRuntimeValue> {
    let mut current = entry;
    let mut guard_stack = guard_stack;
    let mut active_handlers = active_handlers;
    let mut return_frames = return_frames;
    let mut next_guard_id = guard_stack
        .iter()
        .map(|entry| entry.id)
        .max()
        .map_or(0, |id| id + 1);
    // write26: dispatch macro mirrors `cps_eval::dispatch_scope_return!`.
    macro_rules! dispatch_scope_return_repr {
        ($cont:lifetime, $result:expr, $dest:expr) => {{
            match handle_scope_return_repr(
                $result,
                &mut active_handlers,
                &function.name,
                current_eval_id,
            ) {
                ScopeReturnActionRepr::Value(v) => {
                    values.insert(*$dest, v);
                }
                ScopeReturnActionRepr::JumpOrExit { target, value, return_frame_threshold }
                    if target == REPR_EXIT_RWH_TARGET =>
                {
                    if return_frames.len() > return_frame_threshold {
                        return_frames.truncate(return_frame_threshold);
                    }
                    values.insert(*$dest, value);
                }
                ScopeReturnActionRepr::JumpOrExit { target, value, return_frame_threshold } => {
                    if return_frames.len() > return_frame_threshold {
                        return_frames.truncate(return_frame_threshold);
                    }
                    current = target;
                    args = vec![value];
                    continue $cont;
                }
                ScopeReturnActionRepr::Propagate(v) => {
                    if let Some(routed) =
                        try_route_scope_return_through_return_frames_repr(
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
                            owner_function: function.name.clone(),
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
                            owner_function: function.name.clone(),
                            entry: *entry,
                            values: values.clone(),
                            recursive_self: None,
                        }),
                    );
                }
                CpsStmt::MakeRecursiveClosure { dest, entry } => {
                    let closure = CpsReprRuntimeValue::Closure(CpsReprClosure {
                        owner_function: function.name.clone(),
                        entry: *entry,
                        values: values.clone(),
                        recursive_self: Some(*dest),
                    });
                    values.insert(*dest, closure);
                }
                CpsStmt::ForceThunk { dest, thunk } => {
                    // write26 port: loop through nested Thunks, mirroring
                    // cps_eval. A function whose body returns a Thunk-wrapped
                    // body (e.g. `my work() = { ... }` with effect-typed
                    // return) needs to peel through Thunks until a
                    // non-Thunk value (or ScopeReturn) is produced.
                    let mut result = read_value(function, &values, *thunk)?;
                    loop {
                        match result {
                            CpsReprRuntimeValue::Thunk(thunk) => {
                                let handlers = if !active_handlers.is_empty() {
                                    active_handlers.clone()
                                } else {
                                    thunk.handlers
                                };
                                let guards = if !guard_stack.is_empty() {
                                    guard_stack.clone()
                                } else {
                                    thunk.guard_stack
                                };
                                let owner = function_by_name_repr(module, &thunk.owner_function)?;
                                let inherited = return_frames.len();
                                result = eval_continuations(
                                    module,
                                    owner,
                                    thunk.entry,
                                    Vec::new(),
                                    thunk.values,
                                    handlers,
                                    guards,
                                    return_frames.clone(),
                                    inherited,
                                )?;
                                if matches!(result, CpsReprRuntimeValue::ScopeReturn { .. }) {
                                    break;
                                }
                            }
                            _ => break,
                        }
                    }
                    if matches!(result, CpsReprRuntimeValue::Aborted(_)) {
                        return Ok(result);
                    }
                    dispatch_scope_return_repr!('cont, result, dest);
                }
                CpsStmt::InstallHandler {
                    handler,
                    envs,
                    escape,
                } => {
                    let envs = capture_handler_envs(function, &values, envs)?;
                    active_handlers.push(CpsReprHandlerFrame {
                        prompt: fresh_repr_prompt(),
                        handler: *handler,
                        guard_stack: guard_stack.clone(),
                        envs,
                        escape: *escape,
                        escape_owner_function: function.name.clone(),
                        return_frame_threshold: return_frames.len(),
                        inherited: false,
                        install_eval_id: current_eval_id,
                    });
                }
                CpsStmt::UninstallHandler { handler } => {
                    if let Some(pos) = active_handlers
                        .iter()
                        .rposition(|frame| frame.handler == *handler)
                    {
                        active_handlers.remove(pos);
                    }
                }
                CpsStmt::Tuple { dest, items } => {
                    let items = items
                        .iter()
                        .map(|id| read_value(function, &values, *id))
                        .collect::<CpsReprEvalResult<Vec<_>>>()?;
                    values.insert(*dest, CpsReprRuntimeValue::Tuple(items));
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
                        .map(|id| read_value(function, &values, id))
                        .transpose()?
                        .map(Box::new);
                    values.insert(
                        *dest,
                        CpsReprRuntimeValue::Variant {
                            tag: tag.clone(),
                            value,
                        },
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
                    let value = match read_value(function, &values, *tuple)? {
                        CpsReprRuntimeValue::Tuple(items) => items
                            .get(*index)
                            .cloned()
                            .ok_or_else(|| CpsReprEvalError::MissingRecordField {
                                function: function.name.clone(),
                                field: typed_ir::Name(index.to_string()),
                            })?,
                        CpsReprRuntimeValue::Plain(runtime::VmValue::Tuple(items)) => {
                            cps_repr_value_from_vm(items.get(*index).cloned().ok_or_else(|| {
                                CpsReprEvalError::MissingRecordField {
                                    function: function.name.clone(),
                                    field: typed_ir::Name(index.to_string()),
                                }
                            })?)
                        }
                        other => other,
                    };
                    values.insert(*dest, value);
                }
                CpsStmt::VariantTagEq { dest, variant, tag } => {
                    let matches = match read_value(function, &values, *variant)? {
                        CpsReprRuntimeValue::Variant { tag: actual, .. } => actual == *tag,
                        CpsReprRuntimeValue::Plain(runtime::VmValue::Variant {
                            tag: actual,
                            ..
                        }) => actual == *tag,
                        _ => false,
                    };
                    values.insert(
                        *dest,
                        CpsReprRuntimeValue::Plain(runtime::VmValue::Bool(matches)),
                    );
                }
                CpsStmt::VariantPayload { dest, variant } => {
                    let value = match read_value(function, &values, *variant)? {
                        CpsReprRuntimeValue::Variant {
                            value: Some(value), ..
                        } => *value,
                        CpsReprRuntimeValue::Variant { value: None, .. } => {
                            CpsReprRuntimeValue::Plain(runtime::VmValue::Unit)
                        }
                        CpsReprRuntimeValue::Plain(runtime::VmValue::Variant {
                            value: Some(value),
                            ..
                        }) => cps_repr_value_from_vm(*value),
                        CpsReprRuntimeValue::Plain(runtime::VmValue::Variant {
                            value: None,
                            ..
                        }) => CpsReprRuntimeValue::Plain(runtime::VmValue::Unit),
                        other => other,
                    };
                    values.insert(*dest, value);
                }
                CpsStmt::Primitive { dest, op, args } => {
                    let args = args
                        .iter()
                        .map(|id| read_value(function, &values, *id))
                        .collect::<CpsReprEvalResult<Vec<_>>>()?;
                    let result = eval_cps_repr_primitive(*op, args)?;
                    values.insert(*dest, result);
                }
                CpsStmt::DirectCall { dest, target, args } => {
                    let target_function = function_by_name_repr(module, target)?;
                    let args = args
                        .iter()
                        .map(|id| read_value(function, &values, *id))
                        .collect::<CpsReprEvalResult<Vec<_>>>()?;
                    let inherited = return_frames.len();
                    let result = eval_function_with_context(
                        module,
                        target_function,
                        args,
                        active_handlers.clone(),
                        guard_stack.clone(),
                        return_frames.clone(),
                        inherited,
                    )?;
                    if matches!(result, CpsReprRuntimeValue::Aborted(_)) {
                        return Ok(result);
                    }
                    dispatch_scope_return_repr!('cont, result, dest);
                }
                CpsStmt::ApplyClosure { dest, closure, arg } => {
                    let closure = read_closure(function, &values, *closure)?;
                    let arg = read_value(function, &values, *arg)?;
                    let owner = function_by_name_repr(module, &closure.owner_function)?;
                    let mut closure_values = closure.values.clone();
                    if let Some(self_id) = closure.recursive_self {
                        closure_values
                            .insert(self_id, CpsReprRuntimeValue::Closure(closure.clone()));
                    }
                    let inherited = return_frames.len();
                    let result = eval_continuations(
                        module,
                        owner,
                        closure.entry,
                        vec![arg],
                        closure_values,
                        active_handlers.clone(),
                        guard_stack.clone(),
                        return_frames.clone(),
                        inherited,
                    )?;
                    if matches!(result, CpsReprRuntimeValue::Aborted(_)) {
                        return Ok(result);
                    }
                    dispatch_scope_return_repr!('cont, result, dest);
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
                    let owner = function_by_name_repr(module, &resumption.owner_function)?;
                    let anchor = resumption.handled_anchor;
                    let resumed_handlers = merge_resumption_handlers_repr(
                        &resumption.handlers,
                        &active_handlers,
                        anchor,
                    );
                    let adjusted_frames = merge_extras_into_frames_repr(
                        &resumption.return_frames,
                        &active_handlers,
                        anchor,
                    );
                    let result = eval_continuations(
                        module,
                        owner,
                        resumption.target,
                        vec![CpsReprRuntimeValue::Plain(arg)],
                        resumption.values.clone(),
                        resumed_handlers,
                        resumption.guard_stack.clone(),
                        adjusted_frames,
                        0,
                    )?;
                    if matches!(result, CpsReprRuntimeValue::Aborted(_)) {
                        return Ok(result);
                    }
                    dispatch_scope_return_repr!('cont, result, dest);
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
                    let owner = function_by_name_repr(module, &resumption.owner_function)?;
                    // write26: mirror cps_eval's RWH pattern. Push the RWH
                    // frame to local active_handlers with current_eval_id,
                    // construct inner_handlers = captured + [RWH inherited],
                    // and use the dispatch macro on result.
                    let pushed_prompt = fresh_repr_prompt();
                    active_handlers.push(CpsReprHandlerFrame {
                        prompt: pushed_prompt,
                        handler: *handler,
                        guard_stack: guard_stack.clone(),
                        envs,
                        escape: REPR_EXIT_RWH_TARGET,
                        escape_owner_function: function.name.clone(),
                        return_frame_threshold: return_frames.len(),
                        inherited: false,
                        install_eval_id: current_eval_id,
                    });
                    let inner_handlers = {
                        let mut stack = resumption.handlers.clone();
                        let mut owned = active_handlers
                            .last()
                            .cloned()
                            .expect("just pushed RWH frame");
                        owned.inherited = true;
                        stack.push(owned);
                        stack
                    };
                    let result = eval_continuations(
                        module,
                        owner,
                        resumption.target,
                        vec![CpsReprRuntimeValue::Plain(arg)],
                        resumption.values.clone(),
                        inner_handlers,
                        resumption.guard_stack.clone(),
                        resumption.return_frames.clone(),
                        0,
                    )?;
                    if matches!(result, CpsReprRuntimeValue::Aborted(_)) {
                        return Ok(result);
                    }
                    dispatch_scope_return_repr!('cont, result, dest);
                    // Pop the RWH frame in the value-flow path.
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
                let v = read_value(function, &values, *value)?;
                if return_frames.len() <= initial_frame_count {
                    return Ok(v);
                }
                // write26 port of write25 pre-force v2.
                if let CpsReprRuntimeValue::Thunk(_) = &v {
                    let top_index = return_frames.len() - 1;
                    let top_frame = &return_frames[top_index];
                    if return_frame_immediately_forces_param_repr(module, top_frame)?
                        && top_index >= initial_frame_count
                    {
                        let top_frame = top_frame.clone();
                        let top_owner = function_by_name_repr(module, &top_frame.owner_function)?;
                        return resume_continuation(
                            module,
                            top_owner,
                            top_frame.continuation,
                            vec![v],
                            top_frame.values.as_ref().clone(),
                            top_frame.active_handlers.clone(),
                            top_frame.guard_stack.clone(),
                            return_frames.clone(),
                            return_frames.len(),
                            top_frame.owner_eval_id,
                        );
                    }
                }
                return continue_return_frames_repr(module, v, &return_frames, &[]);
            }
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
                let payload = read_plain_value(function, &values, *payload)?;
                let blocked = blocked
                    .map(|blocked| read_effect_id(function, &values, blocked))
                    .transpose()?;
                let handler_stack =
                    handler_stack_with_static(&active_handlers, *handler, &guard_stack);
                let (handler_arm, frame, handler_body_stack, handler_owner) =
                    handler_arm_for_stack(module, function, &handler_stack, effect, blocked)?;
                let handler_values =
                    values_with_handler_env(HashMap::new(), frame, handler_arm.entry);
                let frame_prompt = frame.prompt;
                let frame_escape = frame.escape;
                // write26: a synthetic frame (install_eval=SYNTHETIC) is a
                // virtual fallback created when no real handler is in scope.
                // Even if it ended up in `active_handlers` (via being
                // captured in a prior resumption.handlers), it has no real
                // install scope to dispatch to. Treat the arm body result as
                // this eval frame's value, like the no-handler case.
                let frame_in_active = active_handlers.iter().any(|f| f.prompt == frame_prompt)
                    && frame.install_eval_id != REPR_SYNTHETIC_EVAL_ID;
                let handled_anchor = if frame_in_active {
                    Some(CpsReprHandlerAnchor {
                        prompt: frame.prompt,
                        install_eval_id: frame.install_eval_id,
                    })
                } else {
                    None
                };
                let resumption = CpsReprRuntimeValue::Resumption(CpsReprResumption {
                    owner_function: function.name.clone(),
                    target: *resume,
                    values: values.clone(),
                    handlers: handler_stack.clone(),
                    guard_stack: guard_stack.clone(),
                    return_frames: return_frames.clone(),
                    handled_anchor,
                });
                let result = eval_continuations(
                    module,
                    handler_owner,
                    handler_arm.entry,
                    vec![CpsReprRuntimeValue::Plain(payload), resumption],
                    handler_values,
                    handler_body_stack,
                    guard_stack.clone(),
                    Vec::new(),
                    0,
                )?;
                if !frame_in_active {
                    // Synthetic fallback frame: no installed handler, so the
                    // arm's result is the value of *this* eval frame.
                    return Ok(result);
                }
                // write26: wrap arm body's natural Return as ScopeReturn so
                // handle_scope_return_repr can route to H_sub.escape /
                // walk-based propagation.
                let scope_return = match result {
                    CpsReprRuntimeValue::ScopeReturn { .. } => result,
                    CpsReprRuntimeValue::Aborted(inner) => {
                        // Legacy Aborted: treat as a generic non-local
                        // return targeted at the current Perform's matched
                        // handler scope.
                        CpsReprRuntimeValue::ScopeReturn {
                            prompt: frame_prompt,
                            target: frame_escape,
                            value: inner,
                        }
                    }
                    other => CpsReprRuntimeValue::ScopeReturn {
                        prompt: frame_prompt,
                        target: frame_escape,
                        value: Box::new(other),
                    },
                };
                match handle_scope_return_repr(
                    scope_return,
                    &mut active_handlers,
                    &function.name,
                    current_eval_id,
                ) {
                    ScopeReturnActionRepr::Value(v) => {
                        return Ok(v);
                    }
                    ScopeReturnActionRepr::Propagate(v) => {
                        if let Some(routed) = try_route_scope_return_through_return_frames_repr(
                            module,
                            &v,
                            &return_frames,
                            initial_frame_count,
                        )? {
                            return Ok(routed);
                        }
                        return Ok(v);
                    }
                    ScopeReturnActionRepr::JumpOrExit {
                        target,
                        value,
                        return_frame_threshold,
                    } => {
                        if return_frames.len() > return_frame_threshold {
                            return_frames.truncate(return_frame_threshold);
                        }
                        if target == REPR_EXIT_RWH_TARGET {
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
                let target_function = function_by_name_repr(module, target)?;
                let call_args = arg_ids
                    .iter()
                    .map(|id| read_value(function, &values, *id))
                    .collect::<CpsReprEvalResult<Vec<_>>>()?;
                let pre_push_count = return_frames.len();
                let frame = CpsReprReturnFrame {
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
                let value = read_value(function, &values, *thunk)?;
                match value {
                    CpsReprRuntimeValue::Thunk(thunk) => {
                        let pre_push_count = return_frames.len();
                        let frame = CpsReprReturnFrame {
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
                        let owner = function_by_name_repr(module, &thunk.owner_function)?;
                        let handlers = if !active_handlers.is_empty() {
                            active_handlers.clone()
                        } else {
                            thunk.handlers.clone()
                        };
                        let guards = if !guard_stack.is_empty() {
                            guard_stack.clone()
                        } else {
                            thunk.guard_stack.clone()
                        };
                        return eval_continuations(
                            module,
                            owner,
                            thunk.entry,
                            Vec::new(),
                            thunk.values.clone(),
                            handlers,
                            guards,
                            new_frames,
                            pre_push_count,
                        );
                    }
                    other => {
                        current = *resume;
                        args = vec![other];
                        continue;
                    }
                }
            }
            CpsTerminator::EffectfulApply {
                closure,
                arg,
                resume,
            } => {
                let callable = read_value(function, &values, *closure)?;
                let pre_push_count = return_frames.len();
                let frame = CpsReprReturnFrame {
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
                    CpsReprRuntimeValue::Closure(closure) => {
                        let arg = read_value(function, &values, *arg)?;
                        let owner = function_by_name_repr(module, &closure.owner_function)?;
                        let mut closure_values = closure.values.clone();
                        if let Some(self_id) = closure.recursive_self {
                            closure_values
                                .insert(self_id, CpsReprRuntimeValue::Closure(closure.clone()));
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
                    CpsReprRuntimeValue::Resumption(resumption) => {
                        let arg = read_plain_value(function, &values, *arg)?;
                        let owner = function_by_name_repr(module, &resumption.owner_function)?;
                        let anchor = resumption.handled_anchor;
                        let resumed_handlers = merge_resumption_handlers_repr(
                            &resumption.handlers,
                            &active_handlers,
                            anchor,
                        );
                        let adjusted_res = merge_extras_into_frames_repr(
                            &resumption.return_frames,
                            &active_handlers,
                            anchor,
                        );
                        let mut combined_frames = new_frames;
                        combined_frames.extend(adjusted_res);
                        return eval_continuations(
                            module,
                            owner,
                            resumption.target,
                            vec![CpsReprRuntimeValue::Plain(arg)],
                            resumption.values.clone(),
                            resumed_handlers,
                            resumption.guard_stack.clone(),
                            combined_frames,
                            0,
                        );
                    }
                    _ => {
                        return Err(CpsReprEvalError::ExpectedPlainValue {
                            function: function.name.clone(),
                            id: *closure,
                        });
                    }
                }
            }
        }
    }
}

/// write26: equality on (prompt, install_eval_id) — same as
/// `cps_eval::same_handler_frame`.
fn same_handler_frame_repr(a: &CpsReprHandlerFrame, b: &CpsReprHandlerFrame) -> bool {
    a.prompt == b.prompt && a.install_eval_id == b.install_eval_id
}

/// write26 port of `cps_eval::merge_resumption_handlers`. Place
/// resume-site siblings between the captured prefix through the anchor
/// handler and the captured inner tail.
fn merge_resumption_handlers_repr(
    captured: &[CpsReprHandlerFrame],
    current: &[CpsReprHandlerFrame],
    anchor: Option<CpsReprHandlerAnchor>,
) -> Vec<CpsReprHandlerFrame> {
    let is_anchor = |frame: &CpsReprHandlerFrame, anchor: CpsReprHandlerAnchor| {
        frame.prompt == anchor.prompt && frame.install_eval_id == anchor.install_eval_id
    };
    if let Some(anchor) = anchor {
        if let Some(anchor_index) = captured.iter().position(|f| is_anchor(f, anchor)) {
            let mut merged = Vec::with_capacity(captured.len() + current.len());
            merged.extend(captured[..=anchor_index].iter().cloned());
            for frame in current {
                let in_prefix = merged.iter().any(|m| same_handler_frame_repr(m, frame));
                let in_tail = captured[anchor_index + 1..]
                    .iter()
                    .any(|c| same_handler_frame_repr(c, frame));
                if !in_prefix && !in_tail {
                    merged.push(frame.clone());
                }
            }
            merged.extend(captured[anchor_index + 1..].iter().cloned());
            return merged;
        }
    }
    // Shared-prefix fallback.
    let mut shared = 0;
    while shared < captured.len()
        && shared < current.len()
        && same_handler_frame_repr(&captured[shared], &current[shared])
    {
        shared += 1;
    }
    let mut merged = Vec::with_capacity(captured.len() + current.len());
    merged.extend(captured[..shared].iter().cloned());
    for frame in &current[shared..] {
        if !captured.iter().any(|c| same_handler_frame_repr(c, frame)) {
            merged.push(frame.clone());
        }
    }
    merged.extend(captured[shared..].iter().cloned());
    merged
}

/// write26 port of `cps_eval::merge_extras_into_frames`.
fn merge_extras_into_frames_repr(
    frames: &[CpsReprReturnFrame],
    current: &[CpsReprHandlerFrame],
    anchor: Option<CpsReprHandlerAnchor>,
) -> Vec<CpsReprReturnFrame> {
    frames
        .iter()
        .map(|frame| {
            let merged = merge_resumption_handlers_repr(&frame.active_handlers, current, anchor);
            let mut adjusted = frame.clone();
            adjusted.active_handlers = merged;
            adjusted
        })
        .collect()
}

/// write26 port of `cps_eval::continue_return_frames`.
fn continue_return_frames_repr(
    module: &CpsReprModule,
    value: CpsReprRuntimeValue,
    frames: &[CpsReprReturnFrame],
    extra_handlers: &[CpsReprHandlerFrame],
) -> CpsReprEvalResult<CpsReprRuntimeValue> {
    if frames.is_empty() {
        return Ok(value);
    }
    if matches!(value, CpsReprRuntimeValue::ScopeReturn { .. })
        || matches!(value, CpsReprRuntimeValue::Aborted(_))
    {
        return Ok(value);
    }
    let (frame, rest) = frames.split_last().expect("non-empty");
    let function = function_by_name_repr(module, &frame.owner_function)?;
    let mut combined = frame.active_handlers.clone();
    for extra in extra_handlers {
        if !combined.iter().any(|f| f.prompt == extra.prompt) {
            combined.push(extra.clone());
        }
    }
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

/// write26 port of `cps_eval::return_frame_immediately_forces_param`.
fn return_frame_immediately_forces_param_repr(
    module: &CpsReprModule,
    frame: &CpsReprReturnFrame,
) -> CpsReprEvalResult<bool> {
    let function = function_by_name_repr(module, &frame.owner_function)?;
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

/// write26 port of `cps_eval::try_route_scope_return_through_return_frames`.
fn try_route_scope_return_through_return_frames_repr(
    module: &CpsReprModule,
    scope_return: &CpsReprRuntimeValue,
    return_frames: &[CpsReprReturnFrame],
    initial_frame_count: usize,
) -> CpsReprEvalResult<Option<CpsReprRuntimeValue>> {
    let CpsReprRuntimeValue::ScopeReturn {
        prompt,
        target,
        value,
    } = scope_return
    else {
        return Ok(None);
    };
    let prompt = *prompt;
    let target = *target;
    if target == REPR_EXIT_RWH_TARGET {
        return Ok(None);
    }
    if return_frames.len() <= initial_frame_count {
        return Ok(None);
    }
    for frame_index in (initial_frame_count..return_frames.len()).rev() {
        let frame = &return_frames[frame_index];
        let frame_eval_id = frame.owner_eval_id;
        let frame_owner = &frame.owner_function;
        let Some(handler_index) = frame.active_handlers.iter().rposition(|handler| {
            handler.prompt == prompt && handler.install_eval_id == frame_eval_id
        }) else {
            continue;
        };
        let matched_handler = frame.active_handlers[handler_index].clone();
        if matched_handler.escape_owner_function != *frame_owner {
            continue;
        }
        let mut post_handlers = frame.active_handlers.clone();
        post_handlers.truncate(handler_index);
        let mut rest_frames: Vec<CpsReprReturnFrame> = return_frames[..frame_index].to_vec();
        let threshold = matched_handler.return_frame_threshold;
        if rest_frames.len() > threshold {
            rest_frames.truncate(threshold);
        }
        let owner = function_by_name_repr(module, &frame.owner_function)?;
        let owner_initial = frame.owner_initial_frame_count.min(rest_frames.len());
        let result = resume_continuation(
            module,
            owner,
            matched_handler.escape,
            vec![*value.clone()],
            frame.values.as_ref().clone(),
            post_handlers,
            frame.guard_stack.clone(),
            rest_frames,
            owner_initial,
            frame.owner_eval_id,
        )?;
        return Ok(Some(result));
    }
    Ok(None)
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
        CpsReprRuntimeValue::Resumption(resumption) => Ok(resumption),
        _ => Err(CpsReprEvalError::ExpectedResumption {
            function: function.name.clone(),
            id,
        }),
    }
}

fn into_plain_value(
    function: &CpsReprFunction,
    id: CpsValueId,
    value: CpsReprRuntimeValue,
) -> CpsReprEvalResult<runtime::VmValue> {
    cps_repr_value_to_vm(value).ok_or_else(|| CpsReprEvalError::ExpectedPlainValue {
        function: function.name.clone(),
        id,
    })
}

fn read_closure(
    function: &CpsReprFunction,
    values: &HashMap<CpsValueId, CpsReprRuntimeValue>,
    id: CpsValueId,
) -> CpsReprEvalResult<CpsReprClosure> {
    match read_value(function, values, id)? {
        CpsReprRuntimeValue::Closure(closure) => Ok(closure),
        _ => Err(CpsReprEvalError::ExpectedPlainValue {
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
    /// First-class CPS containers whose elements may themselves be
    /// resumptions, thunks, or closures. Mirrors `CpsRuntimeValue`
    /// in cps_eval and supports `std::undet.once`'s `list<resumption>`
    /// queue and `(k, queue)` tuple pattern.
    List(Rc<Vec<CpsReprRuntimeValue>>),
    Tuple(Vec<CpsReprRuntimeValue>),
    Variant {
        tag: typed_ir::Name,
        value: Option<Box<CpsReprRuntimeValue>>,
    },
    /// Carries a value produced by a handler arm body's non-local return.
    /// Propagated by every internal call site so the eval_function boundary
    /// can unwrap it.
    ///
    /// Deprecated as of write26: kept only for backward-compatibility paths
    /// that have not yet been migrated to `ScopeReturn`. New code should
    /// emit and route `ScopeReturn` instead.
    Aborted(Box<CpsReprRuntimeValue>),
    /// write26: prompt-targeted non-local return, mirrors
    /// `CpsRuntimeValue::ScopeReturn` in cps_eval. Generated by a
    /// `Perform`'s arm body completion and routed by
    /// `handle_scope_return_repr` to the matching handler scope.
    ScopeReturn {
        prompt: CpsReprPromptId,
        target: CpsContinuationId,
        value: Box<CpsReprRuntimeValue>,
    },
}

/// Dynamic prompt id, fresh per `InstallHandler` execution. Mirrors
/// `cps_eval::CpsPromptId`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
struct CpsReprPromptId(u64);

thread_local! {
    static REPR_PROMPT_COUNTER: std::cell::Cell<u64> = const { std::cell::Cell::new(0) };
}

fn fresh_repr_prompt() -> CpsReprPromptId {
    REPR_PROMPT_COUNTER.with(|cell| {
        let id = cell.get();
        cell.set(id + 1);
        CpsReprPromptId(id)
    })
}

/// Identity of an eval frame instance. Mirrors `cps_eval::CpsEvalId`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
struct CpsReprEvalId(u64);

thread_local! {
    static REPR_EVAL_ID_COUNTER: std::cell::Cell<u64> = const { std::cell::Cell::new(0) };
}

fn fresh_repr_eval_id() -> CpsReprEvalId {
    REPR_EVAL_ID_COUNTER.with(|cell| {
        let id = cell.get();
        cell.set(id + 1);
        CpsReprEvalId(id)
    })
}

/// Synthetic-fallback handler frame sentinel. Mirrors
/// `cps_eval::SYNTHETIC_EVAL_ID`.
const REPR_SYNTHETIC_EVAL_ID: CpsReprEvalId = CpsReprEvalId(u64::MAX);

/// Sentinel `target` for `ResumeWithHandler`-installed frames. Mirrors
/// `cps_eval::EXIT_RWH_TARGET`.
const REPR_EXIT_RWH_TARGET: CpsContinuationId = CpsContinuationId(usize::MAX);

/// Anchor used by `merge_resumption_handlers_repr` to position
/// resume-site siblings between captured outer and inner handlers.
/// Mirrors `cps_eval::CpsHandlerAnchor`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct CpsReprHandlerAnchor {
    prompt: CpsReprPromptId,
    install_eval_id: CpsReprEvalId,
}

#[derive(Debug, Clone, PartialEq)]
struct CpsReprResumption {
    owner_function: String,
    target: CpsContinuationId,
    values: HashMap<CpsValueId, CpsReprRuntimeValue>,
    handlers: Vec<CpsReprHandlerFrame>,
    guard_stack: Vec<CpsReprGuardEntry>,
    /// write26: stack of suspended caller continuations captured at
    /// `Perform` time. Mirrors `CpsResumption::return_frames`.
    return_frames: Vec<CpsReprReturnFrame>,
    /// write26: anchor recorded at `Perform` time so resume-site merge
    /// can place siblings at the correct stack depth.
    handled_anchor: Option<CpsReprHandlerAnchor>,
}

#[derive(Debug, Clone, PartialEq)]
struct CpsReprThunk {
    owner_function: String,
    entry: CpsContinuationId,
    values: HashMap<CpsValueId, CpsReprRuntimeValue>,
    handlers: Vec<CpsReprHandlerFrame>,
    guard_stack: Vec<CpsReprGuardEntry>,
}

#[derive(Debug, Clone, PartialEq)]
struct CpsReprClosure {
    owner_function: String,
    entry: CpsContinuationId,
    values: HashMap<CpsValueId, CpsReprRuntimeValue>,
    recursive_self: Option<CpsValueId>,
}

#[derive(Debug, Clone, PartialEq)]
struct CpsReprHandlerFrame {
    /// write26: dynamic prompt id, fresh per scope install.
    prompt: CpsReprPromptId,
    handler: CpsHandlerId,
    guard_stack: Vec<CpsReprGuardEntry>,
    envs: Vec<CpsReprEvaluatedHandlerEnv>,
    /// write26: escape continuation reached when the handler scope
    /// completes via a `ScopeReturn`. `REPR_EXIT_RWH_TARGET` for RWH-
    /// installed frames.
    escape: CpsContinuationId,
    /// write26: function name owning the escape continuation.
    escape_owner_function: String,
    /// write26: `return_frames.len()` at install time. JumpOrExit
    /// truncates frames pushed inside this scope.
    return_frame_threshold: usize,
    /// write26: marks frames inherited via `into_inherited_repr`.
    inherited: bool,
    /// write26: eval frame that installed this handler. Used by
    /// `handle_scope_return_repr` for strict (prompt, install_eval_id)
    /// matching.
    install_eval_id: CpsReprEvalId,
}

#[derive(Debug, Clone, PartialEq)]
struct CpsReprReturnFrame {
    owner_function: String,
    continuation: CpsContinuationId,
    values: Rc<HashMap<CpsValueId, CpsReprRuntimeValue>>,
    active_handlers: Vec<CpsReprHandlerFrame>,
    guard_stack: Vec<CpsReprGuardEntry>,
    owner_initial_frame_count: usize,
    owner_eval_id: CpsReprEvalId,
}

#[derive(Debug, Clone, PartialEq)]
struct CpsReprEvaluatedHandlerEnv {
    entry: CpsContinuationId,
    values: Vec<(CpsValueId, CpsReprRuntimeValue)>,
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
    op: typed_ir::PrimitiveOp,
    args: &[runtime::VmValue],
) -> CpsReprEvalResult<runtime::VmValue> {
    use typed_ir::PrimitiveOp;
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
        _ => runtime::vm::primitive::apply_primitive(op, args)
            .map_err(|_| CpsReprEvalError::UnsupportedPrimitive { op }),
    }
}

fn int_value(op: typed_ir::PrimitiveOp, value: &runtime::VmValue) -> CpsReprEvalResult<i64> {
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

fn bool_value(op: typed_ir::PrimitiveOp, value: &runtime::VmValue) -> CpsReprEvalResult<bool> {
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
                                op: typed_ir::PrimitiveOp::IntAdd,
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
        let effect = typed_ir::Path::from_name(typed_ir::Name("choose".to_string()));
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
                                op: typed_ir::PrimitiveOp::IntAdd,
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
        let effect = typed_ir::Path::from_name(typed_ir::Name("choose".to_string()));
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

    fn blocked_handler_snapshot_module() -> CpsModule {
        let start = typed_ir::Path::from_name(typed_ir::Name("start".to_string()));
        let choose = typed_ir::Path::from_name(typed_ir::Name("choose".to_string()));
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
