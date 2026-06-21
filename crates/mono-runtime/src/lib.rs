//! `mono::Program` をそのまま読む oracle runtime。
//!
//! この crate は control VM の前に `specialize -> mono` 契約を検証するための実行器である。
//! 最適化や軽量 control 表現への lowering は `control-vm` 側で扱う。

#![forbid(unsafe_code)]

use std::collections::{HashMap, HashSet};
use std::fmt;
use std::rc::Rc;

use list_tree::{ListTree, ListView};
use mono::{
    Block, CaseArm, CatchArm, DefId, Expr, ExprKind, FunctionAdapterHygiene, InstanceId, Lit, Pat,
    PrimitiveContext, PrimitiveOp, RangeConstructors, RecordField, RecordPatField, RecordSpread,
    Root, SelectResolution, Stmt, Type,
};
use num_bigint::BigInt;
use text_tree::{BytesTree, StringTree};

mod runtime;
#[cfg(test)]
mod tests;

pub fn run_program(program: &mono::Program) -> Result<Vec<Value>, RuntimeError> {
    Runtime::new(program).run()
}

type RuntimeResult<'a> = Result<EvalResult<'a>, RuntimeError>;
type Continuation<'a> = Rc<dyn Fn(&mut Runtime<'a>, Value) -> RuntimeResult<'a> + 'a>;
type BindResult<'a> = Result<BindEvalResult<'a>, RuntimeError>;
type BindContinuation<'a> =
    Rc<dyn Fn(&mut Runtime<'a>, bool, CapturedEnv) -> RuntimeResult<'a> + 'a>;
type BindStep<'a> = Rc<dyn Fn(&mut Runtime<'a>, bool, CapturedEnv) -> BindResult<'a> + 'a>;
type BindValueStep<'a> = Rc<dyn Fn(&mut Runtime<'a>, Value, CapturedEnv) -> BindResult<'a> + 'a>;
type BindResume<'a> = Rc<dyn Fn(&mut Runtime<'a>, Value) -> BindResult<'a> + 'a>;

enum EvalResult<'a> {
    Value(Value),
    Request(Request<'a>),
}

#[derive(Clone)]
struct Request<'a> {
    path: Vec<String>,
    guard_ids: Vec<GuardId>,
    carried_guard_ids: Vec<GuardId>,
    payload: Value,
    resume: Continuation<'a>,
}

fn request_without_guard_id<'a>(mut request: Request<'a>, guard_id: GuardId) -> Request<'a> {
    request.guard_ids.retain(|id| *id != guard_id);
    request.carried_guard_ids.retain(|id| *id != guard_id);
    request
}

enum BindEvalResult<'a> {
    Done { matched: bool, env: CapturedEnv },
    Request(BindRequest<'a>),
}

#[derive(Clone)]
struct BindRequest<'a> {
    path: Vec<String>,
    guard_ids: Vec<GuardId>,
    carried_guard_ids: Vec<GuardId>,
    payload: Value,
    resume: BindResume<'a>,
}

pub struct Runtime<'a> {
    program: &'a mono::Program,
    instances: HashMap<InstanceId, Value>,
    evaluating_instances: HashSet<InstanceId>,
    continuations: HashMap<ContinuationId, Continuation<'a>>,
    next_continuation_id: u32,
    guard_ids: Vec<GuardId>,
    active_frames: Vec<ActiveFrame>,
    active_add_ids: Vec<ActiveAddIdMarker>,
    active_marker_plans: Vec<Vec<ValueMarker>>,
    next_guard_id: u32,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct GuardId(pub u32);

#[derive(Debug, Clone, PartialEq, Eq)]
struct ActiveFrame {
    id: GuardId,
    handler_path: Option<Vec<String>>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct ActiveAddIdMarker {
    marker: AddIdMarker,
    entry_frame_len: usize,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum ValueMarker {
    Frame { id: GuardId },
    AddId(AddIdMarker),
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct AddIdMarker {
    pub id: GuardId,
    pub path: Vec<String>,
    pub depth: u32,
    pub guard_own_path: bool,
    pub guard_foreign_path: bool,
    pub carry_after_frame: bool,
}

#[derive(Debug, Clone, PartialEq)]
pub enum Value {
    Int(i64),
    BigInt(BigInt),
    Float(f64),
    Str(StringTree),
    Bytes(BytesTree),
    Bool(bool),
    Unit,
    Tuple(Vec<Value>),
    List(ListTree<Rc<Value>>),
    Record(Vec<ValueField>),
    PolyVariant {
        tag: String,
        payloads: Vec<Value>,
    },
    DataConstructor {
        def: DefId,
        payloads: Vec<Value>,
    },
    ConstructorFunction(ConstructorFunction),
    PrimitiveOp(PrimitiveValue),
    Closure(Closure),
    RecursiveClosure {
        def: DefId,
        closure: Closure,
    },
    Thunk(Thunk),
    FunctionAdapter(FunctionAdapter),
    EffectOp {
        path: Vec<String>,
    },
    Continuation(ContinuationId),
    Marked {
        value: Box<Value>,
        markers: Vec<ValueMarker>,
    },
}

#[derive(Debug, Clone, PartialEq)]
pub struct ConstructorFunction {
    pub def: DefId,
    pub arity: usize,
    pub args: Vec<Value>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct PrimitiveValue {
    pub op: PrimitiveOp,
    pub context: PrimitiveContext,
    pub args: Vec<Value>,
}

impl From<&Lit> for Value {
    fn from(lit: &Lit) -> Self {
        match lit {
            Lit::Int(value) => Self::Int(*value),
            Lit::BigInt(value) => Self::BigInt(value.clone()),
            Lit::Float(value) => Self::Float(*value),
            Lit::Str(value) => Self::Str(StringTree::from_str(value)),
            Lit::Bool(value) => Self::Bool(*value),
            Lit::Unit => Self::Unit,
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct ValueField {
    pub name: String,
    pub value: Value,
}

#[derive(Debug, Clone, PartialEq)]
pub struct Closure {
    pub param: Pat,
    pub body: Expr,
    env: CapturedEnv,
}

#[derive(Debug, Clone, PartialEq)]
pub enum Thunk {
    Expr {
        body: Expr,
        env: CapturedEnv,
    },
    Effect {
        path: Vec<String>,
        payload: Box<Value>,
    },
    Continuation {
        id: ContinuationId,
        arg: Box<Value>,
    },
    Value(Box<Value>),
    Adapter {
        source: Type,
        target: Type,
        thunk: Box<Value>,
    },
}

#[derive(Debug, Clone, PartialEq)]
pub struct FunctionAdapter {
    pub source: Type,
    pub target: Type,
    pub function: Box<Value>,
    pub hygiene: FunctionAdapterHygiene,
}

#[derive(Debug, Clone, PartialEq, Default)]
pub struct CapturedEnv {
    locals: HashMap<DefId, Value>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct ContinuationId(pub u32);

#[derive(Debug, Clone, PartialEq)]
pub enum RuntimeError {
    MissingInstance {
        instance: InstanceId,
    },
    MismatchedInstanceSlot {
        requested: InstanceId,
        actual: InstanceId,
    },
    RecursiveInstance {
        instance: InstanceId,
    },
    UnboundLocal {
        def: DefId,
    },
    MissingContinuation {
        id: ContinuationId,
    },
    UnresolvedSelect {
        name: String,
    },
    MissingRecordField {
        name: String,
    },
    NotFunction {
        value: Value,
    },
    NotThunk {
        value: Value,
    },
    ExpectedInt {
        value: Value,
    },
    ExpectedFloat {
        value: Value,
    },
    ExpectedBool {
        value: Value,
    },
    ExpectedRecord {
        value: Value,
    },
    ExpectedList {
        value: Value,
    },
    ExpectedBytes {
        value: Value,
    },
    MissingPrimitiveContext {
        op: PrimitiveOp,
    },
    UnsupportedPrimitive {
        op: PrimitiveOp,
    },
    ExpectedFunctionType,
    PatternMismatch,
    NoMatchingCase,
    NonBoolGuard {
        value: Value,
    },
    UnsupportedExpr {
        feature: String,
    },
    UnsupportedPattern {
        feature: String,
    },
    UnsupportedBoundary {
        feature: String,
    },
    UnhandledEffect {
        path: Vec<String>,
    },
}

impl fmt::Display for RuntimeError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::MissingInstance { instance } => write!(f, "missing instance m{}", instance.0),
            Self::MismatchedInstanceSlot { requested, actual } => write!(
                f,
                "mismatched instance slot: requested m{}, found m{}",
                requested.0, actual.0
            ),
            Self::RecursiveInstance { instance } => {
                write!(f, "recursive instance evaluation m{}", instance.0)
            }
            Self::UnboundLocal { def } => write!(f, "unbound local d{}", def.0),
            Self::MissingContinuation { id } => write!(f, "missing continuation k{}", id.0),
            Self::UnresolvedSelect { name } => write!(f, "unresolved select .{name}"),
            Self::MissingRecordField { name } => write!(f, "missing record field {name}"),
            Self::NotFunction { value } => write!(f, "value is not a function: {value:?}"),
            Self::NotThunk { value } => write!(f, "value is not a thunk: {value:?}"),
            Self::ExpectedInt { value } => write!(f, "expected int, got {value:?}"),
            Self::ExpectedFloat { value } => write!(f, "expected float, got {value:?}"),
            Self::ExpectedBool { value } => write!(f, "expected bool, got {value:?}"),
            Self::ExpectedRecord { value } => write!(f, "expected record, got {value:?}"),
            Self::ExpectedList { value } => write!(f, "expected list, got {value:?}"),
            Self::ExpectedBytes { value } => write!(f, "expected bytes, got {value:?}"),
            Self::MissingPrimitiveContext { op } => {
                write!(f, "missing runtime context for primitive {op:?}")
            }
            Self::UnsupportedPrimitive { op } => write!(f, "unsupported primitive {op:?}"),
            Self::ExpectedFunctionType => write!(f, "expected function type"),
            Self::PatternMismatch => write!(f, "pattern mismatch"),
            Self::NoMatchingCase => write!(f, "no matching case arm"),
            Self::NonBoolGuard { value } => write!(f, "case guard returned non-bool {value:?}"),
            Self::UnsupportedExpr { feature } => write!(f, "unsupported expression: {feature}"),
            Self::UnsupportedPattern { feature } => write!(f, "unsupported pattern: {feature}"),
            Self::UnsupportedBoundary { feature } => write!(f, "unsupported boundary: {feature}"),
            Self::UnhandledEffect { path } => write!(f, "unhandled effect {}", path.join("::")),
        }
    }
}

impl std::error::Error for RuntimeError {}

fn function_parts(ty: &Type) -> Option<(&Type, &Type)> {
    let Type::Fun { arg, ret, .. } = ty else {
        return None;
    };
    Some((arg, ret))
}

fn thunk_value_type(ty: &Type) -> Option<&Type> {
    let Type::Thunk { value, .. } = ty else {
        return None;
    };
    Some(value)
}

fn equivalent_runtime_types(source: &Type, target: &Type) -> bool {
    if source == target || source.is_pure_effect() && target.is_pure_effect() {
        return true;
    }
    match (source, target) {
        (source, Type::Thunk { effect, value }) if effect.is_pure_effect() => {
            equivalent_runtime_types(source, value)
        }
        (Type::Thunk { effect, value }, target) if effect.is_pure_effect() => {
            equivalent_runtime_types(value, target)
        }
        (Type::Record(source_fields), Type::Record(target_fields)) => {
            target_fields.iter().all(|target| {
                mono_record_field_type(source_fields, &target.name)
                    .map_or(target.optional, |source| {
                        equivalent_runtime_types(&source.value, &target.value)
                    })
            })
        }
        (Type::PolyVariant(source_variants), Type::PolyVariant(target_variants)) => {
            source_variants.iter().all(|source| {
                target_variants
                    .iter()
                    .find(|target| {
                        target.name == source.name && target.payloads.len() == source.payloads.len()
                    })
                    .is_some_and(|target| {
                        source
                            .payloads
                            .iter()
                            .zip(&target.payloads)
                            .all(|(source, target)| equivalent_runtime_types(source, target))
                    })
            })
        }
        (source, Type::Union(left, right)) => {
            equivalent_runtime_types(source, left) || equivalent_runtime_types(source, right)
        }
        (Type::Union(left, right), target) => {
            equivalent_runtime_types(left, target) && equivalent_runtime_types(right, target)
        }
        (source, Type::Intersection(left, right)) => {
            equivalent_runtime_types(source, left) && equivalent_runtime_types(source, right)
        }
        (Type::Intersection(left, right), target) => {
            equivalent_runtime_types(left, target) || equivalent_runtime_types(right, target)
        }
        _ => false,
    }
}

fn mono_record_field_type<'a>(
    fields: &'a [mono::TypeField],
    name: &str,
) -> Option<&'a mono::TypeField> {
    fields.iter().find(|field| field.name == name)
}

fn value_boundary_supported(source: &Type, target: &Type) -> bool {
    if equivalent_runtime_types(source, target) || matches!(target, Type::Any) {
        return true;
    }
    if matches!(source, Type::Never) {
        return true;
    }
    match (source, target) {
        (Type::Fun { .. }, Type::Fun { .. }) => function_boundary_supported(source, target),
        (Type::Thunk { value: source, .. }, Type::Thunk { value: target, .. }) => {
            value_boundary_supported(source, target)
        }
        (Type::Thunk { value: source, .. }, target) => value_boundary_supported(source, target),
        (source, Type::Thunk { value: target, .. }) => value_boundary_supported(source, target),
        (Type::Record(source_fields), Type::Record(target_fields)) => {
            record_value_boundary_supported(source_fields, target_fields)
        }
        _ => false,
    }
}

fn function_boundary_supported(source: &Type, target: &Type) -> bool {
    let Some((source_arg, source_ret)) = function_parts(source) else {
        return false;
    };
    let Some((target_arg, target_ret)) = function_parts(target) else {
        return false;
    };
    value_boundary_supported(target_arg, source_arg)
        && value_boundary_supported(source_ret, target_ret)
}

fn record_value_boundary_supported(
    source_fields: &[mono::TypeField],
    target_fields: &[mono::TypeField],
) -> bool {
    target_fields.iter().all(|target| {
        mono_record_field_type(source_fields, &target.name).map_or(target.optional, |source| {
            value_boundary_supported(&source.value, &target.value)
        })
    })
}

fn record_field_with_index<'a>(
    fields: &'a [ValueField],
    name: &str,
) -> Option<(usize, &'a ValueField)> {
    fields
        .iter()
        .enumerate()
        .rev()
        .find(|(_, field)| field.name == name)
}

fn markers_for_function_call(markers: Vec<ValueMarker>) -> Vec<ValueMarker> {
    dedupe_markers(
        markers
            .into_iter()
            .map(|marker| match marker {
                ValueMarker::Frame { id } => ValueMarker::Frame { id },
                ValueMarker::AddId(marker) => ValueMarker::AddId(AddIdMarker {
                    depth: marker.depth.saturating_sub(1),
                    ..marker
                }),
            })
            .collect(),
    )
}

fn markers_for_continuation_call(markers: Vec<ValueMarker>) -> Vec<ValueMarker> {
    dedupe_markers(
        markers
            .into_iter()
            .map(|marker| match marker {
                ValueMarker::Frame { id } => ValueMarker::Frame { id },
                ValueMarker::AddId(marker) => ValueMarker::AddId(AddIdMarker {
                    depth: marker.depth.saturating_sub(1),
                    guard_own_path: false,
                    guard_foreign_path: true,
                    ..marker
                }),
            })
            .collect(),
    )
}

fn markers_for_continuation_resume(markers: &[ValueMarker]) -> Vec<ValueMarker> {
    dedupe_markers(
        markers
            .iter()
            .cloned()
            .map(|marker| match marker {
                ValueMarker::AddId(marker) => ValueMarker::AddId(AddIdMarker {
                    guard_own_path: false,
                    guard_foreign_path: true,
                    ..marker
                }),
                marker => marker,
            })
            .collect(),
    )
}

fn markers_for_value(markers: &[ValueMarker]) -> Vec<ValueMarker> {
    dedupe_markers(markers.to_vec())
}

fn markers_for_created_value(markers: &[ValueMarker], value: &Value) -> Vec<ValueMarker> {
    if !value_is_thunk_like(value) {
        return markers_for_value(markers);
    }
    markers_for_value(markers)
}

fn stack_handler_markers(id: GuardId, path: Vec<String>) -> Vec<ValueMarker> {
    vec![
        ValueMarker::Frame { id },
        ValueMarker::AddId(AddIdMarker {
            id,
            path: path.clone(),
            depth: 0,
            guard_own_path: false,
            guard_foreign_path: true,
            carry_after_frame: false,
        }),
        ValueMarker::AddId(AddIdMarker {
            id,
            path,
            depth: 1,
            guard_own_path: true,
            guard_foreign_path: true,
            carry_after_frame: false,
        }),
    ]
}

fn request_path_carries_function_adapter_guard(path: &[String]) -> bool {
    path_has_str_prefix(path, &["std", "control", "flow", "sub"])
        || path_has_str_prefix(path, &["std", "control", "flow", "label_sub"])
}

fn mark_value(value: Value, markers: &[ValueMarker]) -> Value {
    if markers.is_empty() {
        return value;
    }

    let (value, mut value_markers) = into_value_markers(value);
    extend_marker_list(&mut value_markers, markers);
    if value_markers.is_empty() || is_scalar_value(&value) {
        return value;
    }
    Value::Marked {
        value: Box::new(value),
        markers: value_markers,
    }
}

fn recursive_let_value(pat: &Pat, value: Value) -> Value {
    let (value, markers) = into_value_markers(value);
    let value = match (pat, value) {
        (Pat::Var(def), Value::Closure(closure)) => Value::RecursiveClosure { def: *def, closure },
        (_, value) => value,
    };
    mark_value(value, &markers)
}

fn strip_value_markers(value: Value) -> Value {
    into_value_markers(value).0
}

fn value_view(value: &Value) -> (&Value, Vec<ValueMarker>) {
    let mut value = value;
    let mut markers = Vec::new();
    while let Value::Marked {
        value: inner,
        markers: value_markers,
    } = value
    {
        extend_marker_list(&mut markers, value_markers);
        value = inner;
    }
    (value, markers)
}

fn value_is_thunk_like(value: &Value) -> bool {
    match value {
        Value::Thunk(_) => true,
        Value::Marked { value, .. } => value_is_thunk_like(value),
        _ => false,
    }
}

fn path_has_prefix(path: &[String], prefix: &[String]) -> bool {
    prefix.len() <= path.len()
        && path
            .iter()
            .zip(prefix)
            .all(|(segment, prefix)| segment == prefix)
}

fn path_has_str_prefix(path: &[String], prefix: &[&str]) -> bool {
    prefix.len() <= path.len()
        && path
            .iter()
            .zip(prefix)
            .all(|(segment, prefix)| segment == prefix)
}

fn into_value_markers(value: Value) -> (Value, Vec<ValueMarker>) {
    let mut value = value;
    let mut markers = Vec::new();
    while let Value::Marked {
        value: inner,
        markers: value_markers,
    } = value
    {
        extend_marker_list(&mut markers, &value_markers);
        value = *inner;
    }
    (value, markers)
}

fn extend_marker_list(markers: &mut Vec<ValueMarker>, new_markers: &[ValueMarker]) {
    for marker in new_markers {
        if !markers.iter().any(|existing| existing == marker) {
            markers.push(marker.clone());
        }
    }
}

fn dedupe_markers(markers: Vec<ValueMarker>) -> Vec<ValueMarker> {
    let mut deduped = Vec::new();
    extend_marker_list(&mut deduped, &markers);
    deduped
}

fn is_scalar_value(value: &Value) -> bool {
    matches!(
        value,
        Value::Int(_)
            | Value::BigInt(_)
            | Value::Float(_)
            | Value::Str(_)
            | Value::Bytes(_)
            | Value::Bool(_)
            | Value::Unit
    )
}

fn value_equivalent(left: &Value, right: &Value) -> bool {
    let (left, _) = value_view(left);
    let (right, _) = value_view(right);
    left == right
}

fn constructor_value(def: DefId, arity: usize, args: Vec<Value>) -> Value {
    if args.len() >= arity {
        return Value::DataConstructor {
            def,
            payloads: args,
        };
    }
    Value::ConstructorFunction(ConstructorFunction { def, arity, args })
}

fn apply_constructor(mut constructor: ConstructorFunction, arg: Value) -> Value {
    constructor.args.push(arg);
    constructor_value(constructor.def, constructor.arity, constructor.args)
}

fn apply_primitive(
    op: PrimitiveOp,
    context: &PrimitiveContext,
    args: &[Value],
) -> Result<Value, RuntimeError> {
    match op {
        PrimitiveOp::YadaYada => Err(RuntimeError::UnsupportedPrimitive { op }),
        PrimitiveOp::BoolNot => Ok(Value::Bool(!expect_bool(&args[0])?)),
        PrimitiveOp::BoolEq => Ok(Value::Bool(
            expect_bool(&args[0])? == expect_bool(&args[1])?,
        )),
        PrimitiveOp::IntAdd => Ok(Value::Int(expect_int(&args[0])? + expect_int(&args[1])?)),
        PrimitiveOp::IntSub => Ok(Value::Int(expect_int(&args[0])? - expect_int(&args[1])?)),
        PrimitiveOp::IntMul => Ok(Value::Int(expect_int(&args[0])? * expect_int(&args[1])?)),
        PrimitiveOp::IntDiv => Ok(Value::Int(expect_int(&args[0])? / expect_int(&args[1])?)),
        PrimitiveOp::IntMod => Ok(Value::Int(expect_int(&args[0])? % expect_int(&args[1])?)),
        PrimitiveOp::IntEq => Ok(Value::Bool(expect_int(&args[0])? == expect_int(&args[1])?)),
        PrimitiveOp::IntLt => Ok(Value::Bool(expect_int(&args[0])? < expect_int(&args[1])?)),
        PrimitiveOp::IntLe => Ok(Value::Bool(expect_int(&args[0])? <= expect_int(&args[1])?)),
        PrimitiveOp::IntGt => Ok(Value::Bool(expect_int(&args[0])? > expect_int(&args[1])?)),
        PrimitiveOp::IntGe => Ok(Value::Bool(expect_int(&args[0])? >= expect_int(&args[1])?)),
        PrimitiveOp::FloatAdd => Ok(Value::Float(
            expect_float(&args[0])? + expect_float(&args[1])?,
        )),
        PrimitiveOp::FloatSub => Ok(Value::Float(
            expect_float(&args[0])? - expect_float(&args[1])?,
        )),
        PrimitiveOp::FloatMul => Ok(Value::Float(
            expect_float(&args[0])? * expect_float(&args[1])?,
        )),
        PrimitiveOp::FloatDiv => Ok(Value::Float(
            expect_float(&args[0])? / expect_float(&args[1])?,
        )),
        PrimitiveOp::FloatEq => Ok(Value::Bool(
            expect_float(&args[0])? == expect_float(&args[1])?,
        )),
        PrimitiveOp::FloatLt => Ok(Value::Bool(
            expect_float(&args[0])? < expect_float(&args[1])?,
        )),
        PrimitiveOp::FloatLe => Ok(Value::Bool(
            expect_float(&args[0])? <= expect_float(&args[1])?,
        )),
        PrimitiveOp::FloatGt => Ok(Value::Bool(
            expect_float(&args[0])? > expect_float(&args[1])?,
        )),
        PrimitiveOp::FloatGe => Ok(Value::Bool(
            expect_float(&args[0])? >= expect_float(&args[1])?,
        )),
        PrimitiveOp::StringEq => Ok(Value::Bool(expect_str(&args[0])? == expect_str(&args[1])?)),
        PrimitiveOp::StringConcat => Ok(Value::Str(StringTree::concat(
            expect_str(&args[0])?.clone(),
            expect_str(&args[1])?.clone(),
        ))),
        PrimitiveOp::StringLen => Ok(Value::Int(expect_str(&args[0])?.len() as i64)),
        PrimitiveOp::StringLineCount => Ok(Value::Int(expect_str(&args[0])?.line_count() as i64)),
        PrimitiveOp::StringLineRange => {
            let text = expect_str(&args[0])?;
            let index = value_index(&args[1])?;
            let next = index
                .checked_add(1)
                .ok_or_else(|| RuntimeError::UnsupportedBoundary {
                    feature: "line index overflow".to_string(),
                })?;
            text.line_range(index, next)
                .map(|range| range_value(context, op, range.start, range.end))
                .transpose()?
                .ok_or_else(|| RuntimeError::UnsupportedBoundary {
                    feature: format!("line {index} out of bounds"),
                })
        }
        PrimitiveOp::StringIndex => {
            let index = value_index(&args[1])?;
            expect_str(&args[0])?
                .index(index)
                .map(StringTree::from)
                .map(Value::Str)
                .ok_or_else(|| RuntimeError::UnsupportedPrimitive { op })
        }
        PrimitiveOp::StringIndexRange => {
            let text = expect_str(&args[0])?;
            let (start, end) = normalized_range_value(context, op, &args[1], text.len())?;
            text.index_range(start, end)
                .map(Value::Str)
                .ok_or_else(|| RuntimeError::UnsupportedPrimitive { op })
        }
        PrimitiveOp::StringIndexRangeRaw => {
            let start = value_index(&args[1])?;
            let end = value_index(&args[2])?;
            expect_str(&args[0])?
                .index_range(start, end)
                .map(Value::Str)
                .ok_or_else(|| RuntimeError::UnsupportedPrimitive { op })
        }
        PrimitiveOp::StringSplice => {
            let text = expect_str(&args[0])?;
            let (start, end) = normalized_range_value(context, op, &args[1], text.len())?;
            let insert = expect_str(&args[2])?.clone();
            text.splice(start, end, insert)
                .map(Value::Str)
                .ok_or_else(|| RuntimeError::UnsupportedPrimitive { op })
        }
        PrimitiveOp::StringSpliceRaw => {
            let start = value_index(&args[1])?;
            let end = value_index(&args[2])?;
            let insert = expect_str(&args[3])?.clone();
            expect_str(&args[0])?
                .splice(start, end, insert)
                .map(Value::Str)
                .ok_or_else(|| RuntimeError::UnsupportedPrimitive { op })
        }
        PrimitiveOp::StringToBytes => Ok(Value::Bytes(BytesTree::from_bytes(
            expect_str(&args[0])?.to_flat_string().as_bytes(),
        ))),
        PrimitiveOp::IntToString => Ok(Value::Str(StringTree::from(
            expect_int(&args[0])?.to_string(),
        ))),
        PrimitiveOp::IntToHex => Ok(Value::Str(StringTree::from(format!(
            "{:x}",
            expect_int(&args[0])?
        )))),
        PrimitiveOp::IntToUpperHex => Ok(Value::Str(StringTree::from(format!(
            "{:X}",
            expect_int(&args[0])?
        )))),
        PrimitiveOp::IntToFloat => Ok(Value::Float(expect_int(&args[0])? as f64)),
        PrimitiveOp::FloatToString => Ok(Value::Str(StringTree::from(format_float(expect_float(
            &args[0],
        )?)))),
        PrimitiveOp::BoolToString => Ok(Value::Str(StringTree::from(
            expect_bool(&args[0])?.to_string(),
        ))),
        PrimitiveOp::ListEmpty => Ok(Value::List(ListTree::empty())),
        PrimitiveOp::ListSingleton => {
            Ok(Value::List(ListTree::singleton(Rc::new(args[0].clone()))))
        }
        PrimitiveOp::ListLen => Ok(Value::Int(expect_list(&args[0])?.len() as i64)),
        PrimitiveOp::ListMerge => Ok(Value::List(ListTree::concat(
            expect_list(&args[0])?.clone(),
            expect_list(&args[1])?.clone(),
        ))),
        PrimitiveOp::ListIndex => {
            let index = value_index(&args[1])?;
            expect_list(&args[0])?
                .index(index)
                .map(|value| (*value).clone())
                .ok_or_else(|| RuntimeError::ExpectedList {
                    value: args[0].clone(),
                })
        }
        PrimitiveOp::ListIndexRange => {
            let list = expect_list(&args[0])?;
            let (start, end) = normalized_range_value(context, op, &args[1], list.len())?;
            list.index_range(start, end)
                .map(Value::List)
                .ok_or_else(|| RuntimeError::ExpectedList {
                    value: args[0].clone(),
                })
        }
        PrimitiveOp::ListIndexRangeRaw => {
            let start = value_index(&args[1])?;
            let end = value_index(&args[2])?;
            expect_list(&args[0])?
                .index_range(start, end)
                .map(Value::List)
                .ok_or_else(|| RuntimeError::ExpectedList {
                    value: args[0].clone(),
                })
        }
        PrimitiveOp::ListSplice => {
            let list = expect_list(&args[0])?;
            let (start, end) = normalized_range_value(context, op, &args[1], list.len())?;
            let insert = expect_list(&args[2])?;
            list.splice(start, end, insert.clone())
                .map(Value::List)
                .ok_or_else(|| RuntimeError::ExpectedList {
                    value: args[0].clone(),
                })
        }
        PrimitiveOp::ListSpliceRaw => {
            let start = value_index(&args[1])?;
            let end = value_index(&args[2])?;
            let insert = expect_list(&args[3])?;
            expect_list(&args[0])?
                .splice(start, end, insert.clone())
                .map(Value::List)
                .ok_or_else(|| RuntimeError::ExpectedList {
                    value: args[0].clone(),
                })
        }
        PrimitiveOp::ListViewRaw => apply_list_view_raw(context, &args[0]),
        PrimitiveOp::CharEq => Ok(Value::Bool(expect_str(&args[0])? == expect_str(&args[1])?)),
        PrimitiveOp::CharToString => Ok(Value::Str(expect_str(&args[0])?.clone())),
        PrimitiveOp::CharIsWhitespace => Ok(Value::Bool(
            expect_str(&args[0])?.to_flat_string().trim().is_empty(),
        )),
        PrimitiveOp::CharIsPunctuation => Ok(Value::Bool(
            expect_str(&args[0])?
                .to_flat_string()
                .chars()
                .all(|ch| ch.is_ascii_punctuation()),
        )),
        PrimitiveOp::CharIsWord => Ok(Value::Bool(
            expect_str(&args[0])?
                .to_flat_string()
                .chars()
                .all(|ch| ch == '_' || ch.is_alphanumeric()),
        )),
        PrimitiveOp::BytesLen => Ok(Value::Int(expect_bytes(&args[0])?.len() as i64)),
        PrimitiveOp::BytesEq => Ok(Value::Bool(
            expect_bytes(&args[0])? == expect_bytes(&args[1])?,
        )),
        PrimitiveOp::BytesConcat => Ok(Value::Bytes(BytesTree::concat(
            expect_bytes(&args[0])?.clone(),
            expect_bytes(&args[1])?.clone(),
        ))),
        PrimitiveOp::BytesIndex => {
            let index = value_index(&args[1])?;
            expect_bytes(&args[0])?
                .index(index)
                .map(|byte| Value::Int(byte as i64))
                .ok_or_else(|| RuntimeError::ExpectedBytes {
                    value: args[0].clone(),
                })
        }
        PrimitiveOp::BytesIndexRange => {
            let bytes = expect_bytes(&args[0])?;
            let (start, end) = normalized_range_value(context, op, &args[1], bytes.len())?;
            bytes
                .index_range(start, end)
                .map(Value::Bytes)
                .ok_or_else(|| RuntimeError::ExpectedBytes {
                    value: args[0].clone(),
                })
        }
        PrimitiveOp::BytesToUtf8Raw => {
            let bytes = expect_bytes(&args[0])?.to_flat_vec();
            match std::str::from_utf8(&bytes) {
                Ok(text) => Ok(Value::Tuple(vec![
                    Value::Str(StringTree::from(text)),
                    Value::Int(bytes.len() as i64),
                ])),
                Err(error) => {
                    let valid = error.valid_up_to();
                    let text = std::str::from_utf8(&bytes[..valid]).unwrap_or("");
                    Ok(Value::Tuple(vec![
                        Value::Str(StringTree::from(text)),
                        Value::Int(valid as i64),
                    ]))
                }
            }
        }
        PrimitiveOp::BytesToPath | PrimitiveOp::PathToBytes => {
            Err(RuntimeError::UnsupportedPrimitive { op })
        }
    }
}

fn apply_list_view_raw(context: &PrimitiveContext, value: &Value) -> Result<Value, RuntimeError> {
    let constructors = context
        .list_view
        .ok_or(RuntimeError::MissingPrimitiveContext {
            op: PrimitiveOp::ListViewRaw,
        })?;
    match expect_list(value)?.view() {
        ListView::Empty => Ok(Value::DataConstructor {
            def: constructors.empty,
            payloads: Vec::new(),
        }),
        ListView::Leaf(value) => Ok(Value::DataConstructor {
            def: constructors.leaf,
            payloads: vec![(*value).clone()],
        }),
        ListView::Node { left, right, .. } => Ok(Value::DataConstructor {
            def: constructors.node,
            payloads: vec![Value::List(left), Value::List(right)],
        }),
    }
}

fn range_constructors(
    context: &PrimitiveContext,
    op: PrimitiveOp,
) -> Result<RangeConstructors, RuntimeError> {
    context
        .range
        .ok_or(RuntimeError::MissingPrimitiveContext { op })
}

fn range_value(
    context: &PrimitiveContext,
    op: PrimitiveOp,
    start: usize,
    end: usize,
) -> Result<Value, RuntimeError> {
    let constructors = range_constructors(context, op)?;
    let start = Value::DataConstructor {
        def: constructors.included,
        payloads: vec![Value::Int(index_to_int(start)?)],
    };
    let end = Value::DataConstructor {
        def: constructors.excluded,
        payloads: vec![Value::Int(index_to_int(end)?)],
    };
    Ok(Value::DataConstructor {
        def: constructors.within,
        payloads: vec![start, end],
    })
}

fn normalized_range_value(
    context: &PrimitiveContext,
    op: PrimitiveOp,
    value: &Value,
    len: usize,
) -> Result<(usize, usize), RuntimeError> {
    let constructors = range_constructors(context, op)?;
    let (view, _) = value_view(value);
    let Value::DataConstructor { def, payloads } = view else {
        return Err(RuntimeError::UnsupportedBoundary {
            feature: format!("expected range, got {view:?}"),
        });
    };
    if *def != constructors.within {
        return Err(RuntimeError::UnsupportedBoundary {
            feature: format!("expected range::within, got {view:?}"),
        });
    }
    let Some((start_bound, end_bound)) = range_bound_pair(payloads) else {
        return Err(RuntimeError::UnsupportedBoundary {
            feature: format!("expected range payload pair, got {view:?}"),
        });
    };
    let start = range_start_bound(&constructors, start_bound)?;
    let end = range_end_bound(&constructors, end_bound, len)?;
    if start <= end && end <= len {
        return Ok((start, end));
    }
    Err(RuntimeError::UnsupportedBoundary {
        feature: format!("range {start}..{end} out of bounds for length {len}"),
    })
}

fn range_bound_pair(payloads: &[Value]) -> Option<(&Value, &Value)> {
    match payloads {
        [start, end] => Some((start, end)),
        [payload] => {
            let (payload, _) = value_view(payload);
            let Value::Tuple(bounds) = payload else {
                return None;
            };
            match bounds.as_slice() {
                [start, end] => Some((start, end)),
                _ => None,
            }
        }
        _ => None,
    }
}

fn range_start_bound(
    constructors: &RangeConstructors,
    value: &Value,
) -> Result<usize, RuntimeError> {
    let (view, _) = value_view(value);
    let Value::DataConstructor { def, payloads } = view else {
        return Err(RuntimeError::UnsupportedBoundary {
            feature: format!("expected range bound, got {view:?}"),
        });
    };
    if *def == constructors.unbounded {
        return Ok(0);
    }
    if *def == constructors.included {
        return single_index_payload(payloads);
    }
    if *def == constructors.excluded {
        return single_index_payload(payloads)?
            .checked_add(1)
            .ok_or_else(|| RuntimeError::UnsupportedBoundary {
                feature: "range start bound overflow".to_string(),
            });
    }
    Err(RuntimeError::UnsupportedBoundary {
        feature: format!("expected range bound, got {view:?}"),
    })
}

fn range_end_bound(
    constructors: &RangeConstructors,
    value: &Value,
    len: usize,
) -> Result<usize, RuntimeError> {
    let (view, _) = value_view(value);
    let Value::DataConstructor { def, payloads } = view else {
        return Err(RuntimeError::UnsupportedBoundary {
            feature: format!("expected range bound, got {view:?}"),
        });
    };
    if *def == constructors.unbounded {
        return Ok(len);
    }
    if *def == constructors.included {
        return single_index_payload(payloads)?
            .checked_add(1)
            .ok_or_else(|| RuntimeError::UnsupportedBoundary {
                feature: "range end bound overflow".to_string(),
            });
    }
    if *def == constructors.excluded {
        return single_index_payload(payloads);
    }
    Err(RuntimeError::UnsupportedBoundary {
        feature: format!("expected range bound, got {view:?}"),
    })
}

fn single_index_payload(payloads: &[Value]) -> Result<usize, RuntimeError> {
    if payloads.len() != 1 {
        return Err(RuntimeError::UnsupportedBoundary {
            feature: format!("expected one int payload, got {payloads:?}"),
        });
    }
    value_index(&payloads[0])
}

fn value_index(value: &Value) -> Result<usize, RuntimeError> {
    usize::try_from(expect_int(value)?).map_err(|_| RuntimeError::ExpectedInt {
        value: value.clone(),
    })
}

fn index_to_int(index: usize) -> Result<i64, RuntimeError> {
    i64::try_from(index).map_err(|_| RuntimeError::UnsupportedBoundary {
        feature: format!("index {index} does not fit in int"),
    })
}

fn expect_int(value: &Value) -> Result<i64, RuntimeError> {
    let (value, _) = value_view(value);
    match value {
        Value::Int(value) => Ok(*value),
        Value::BigInt(value) => value
            .to_string()
            .parse()
            .map_err(|_| RuntimeError::ExpectedInt {
                value: Value::BigInt(value.clone()),
            }),
        value => Err(RuntimeError::ExpectedInt {
            value: value.clone(),
        }),
    }
}

fn expect_float(value: &Value) -> Result<f64, RuntimeError> {
    let (value, _) = value_view(value);
    match value {
        Value::Float(value) => Ok(*value),
        Value::Int(value) => Ok(*value as f64),
        value => Err(RuntimeError::ExpectedFloat {
            value: value.clone(),
        }),
    }
}

fn expect_bool(value: &Value) -> Result<bool, RuntimeError> {
    let (value, _) = value_view(value);
    match value {
        Value::Bool(value) => Ok(*value),
        value => Err(RuntimeError::ExpectedBool {
            value: value.clone(),
        }),
    }
}

fn expect_str(value: &Value) -> Result<&StringTree, RuntimeError> {
    let (value, _) = value_view(value);
    match value {
        Value::Str(value) => Ok(value),
        value => Err(RuntimeError::UnsupportedBoundary {
            feature: format!("expected str, got {value:?}"),
        }),
    }
}

fn expect_bytes(value: &Value) -> Result<&BytesTree, RuntimeError> {
    let (value, _) = value_view(value);
    match value {
        Value::Bytes(value) => Ok(value),
        value => Err(RuntimeError::ExpectedBytes {
            value: value.clone(),
        }),
    }
}

fn expect_list(value: &Value) -> Result<&ListTree<Rc<Value>>, RuntimeError> {
    let (value, _) = value_view(value);
    match value {
        Value::List(value) => Ok(value),
        value => Err(RuntimeError::ExpectedList {
            value: value.clone(),
        }),
    }
}

fn format_float(value: f64) -> String {
    let text = value.to_string();
    if text.contains('.') || text.contains('e') || text.contains('E') {
        text
    } else {
        format!("{text}.0")
    }
}

fn value_result<'a>(value: Value) -> RuntimeResult<'a> {
    Ok(EvalResult::Value(value))
}

fn bind_done<'a>(matched: bool, env: CapturedEnv) -> BindResult<'a> {
    Ok(BindEvalResult::Done { matched, env })
}

fn expect_eval_value(result: EvalResult<'_>) -> Result<Value, RuntimeError> {
    match result {
        EvalResult::Value(value) => Ok(value),
        EvalResult::Request(request) => Err(RuntimeError::UnhandledEffect { path: request.path }),
    }
}
