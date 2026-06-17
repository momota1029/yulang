//! Runtime for the lowered control IR.

use std::collections::{HashMap, HashSet};
use std::fmt;
use std::rc::Rc;

use list_tree::{ListTree, ListView};
use mono::{FunctionAdapterHygiene, Lit, PrimitiveContext, PrimitiveOp, Type};
use num_bigint::BigInt;

use crate::boundary::{
    equivalent_runtime_types, function_parts, thunk_value_type, value_boundary_supported,
};
use crate::ir::{
    Block, CaseArm, CatchArm, DefId, Expr, ExprId, InstanceId, Pat, Program, RecordField,
    RecordPatField, RecordSpread, Root, SelectResolution, Stmt,
};
use crate::lower::{LowerError, lower};
use crate::validate::{ValidateError, validate};

mod bind;
mod engine;
mod eval;
mod flow;
mod thunk;

use engine::Runtime;

pub fn run_mono_program(program: &mono::Program) -> Result<Vec<Value>, RunError> {
    let program = lower(program).map_err(RunError::Lower)?;
    run_program(&program)
}

pub fn run_program(program: &Program) -> Result<Vec<Value>, RunError> {
    validate(program).map_err(RunError::Validate)?;
    Runtime::new(program).run().map_err(RunError::Runtime)
}

pub fn run_program_with_host<F>(program: &Program, mut host: F) -> Result<Vec<Value>, RunError>
where
    F: FnMut(&[String], &Value) -> Option<Value>,
{
    run_program_with_host_and_stats(program, &mut host).map(|(values, _)| values)
}

pub fn run_program_with_host_and_stats<F>(
    program: &Program,
    host: &mut F,
) -> Result<(Vec<Value>, RuntimeStats), RunError>
where
    F: FnMut(&[String], &Value) -> Option<Value>,
{
    validate(program).map_err(RunError::Validate)?;
    let mut runtime = Runtime::new(program);
    let values = runtime.run_with_host(host).map_err(RunError::Runtime)?;
    Ok((values, runtime.stats))
}

#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct RuntimeStats {
    pub expr_evals: u64,
    /// Full `Expr` clones performed by eval. This should stay at zero on the dispatch path.
    pub expr_clones: u64,
    pub apply_value_calls: u64,
    pub apply_marked_calls: u64,
    pub apply_primitive_calls: u64,
    pub apply_constructor_calls: u64,
    pub apply_closure_calls: u64,
    pub apply_recursive_closure_calls: u64,
    pub apply_adapter_calls: u64,
    pub apply_forced_thunk_calls: u64,
    pub apply_effect_op_calls: u64,
    pub apply_continuation_calls: u64,
    pub primitive_zero_arity_calls: u64,
    pub primitive_apply_calls: u64,
    pub primitive_apply_partial: u64,
    pub primitive_apply_complete: u64,
    pub force_thunk_calls: u64,
    pub force_marked_calls: u64,
    pub force_expr_calls: u64,
    pub force_value_calls: u64,
    pub force_effect_calls: u64,
    pub force_continuation_calls: u64,
    pub force_adapter_calls: u64,
    pub effect_requests: u64,
    pub host_requests: u64,
    pub catch_request_matches: u64,
    pub continuations_stored: u64,
    pub continuation_invocations: u64,
    pub request_resume_steps: u64,
    pub continue_with_values: u64,
    pub continue_with_requests: u64,
    pub continue_bind_values: u64,
    pub continue_bind_requests: u64,
    pub continue_bind_result_values: u64,
    pub continue_bind_result_requests: u64,
    pub continue_value_bind_values: u64,
    pub continue_value_bind_requests: u64,
    pub marker_frame_calls: u64,
    pub marker_frame_empty: u64,
    pub marker_frame_pushes: u64,
    pub marker_frame_value_closes: u64,
    pub marker_frame_request_closes: u64,
    pub marker_frame_resume_steps: u64,
    pub instance_eval_calls: u64,
    pub instance_cache_hits: u64,
    pub instance_cache_misses: u64,
    pub path_prefix_checks: u64,
    pub path_prefix_segments: u64,
    pub path_eq_checks: u64,
    pub path_eq_segments: u64,
    pub active_add_id_scans: u64,
    pub active_frame_scans: u64,
}

#[derive(Debug, Clone, PartialEq)]
pub enum RunError {
    Lower(LowerError),
    Validate(ValidateError),
    Runtime(RuntimeError),
}

impl fmt::Display for RunError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Lower(error) => write!(f, "{error}"),
            Self::Validate(error) => write!(f, "{error}"),
            Self::Runtime(error) => write!(f, "{error}"),
        }
    }
}

impl std::error::Error for RunError {}

#[derive(Debug, Clone, PartialEq)]
pub enum Value {
    Int(i64),
    BigInt(BigInt),
    Float(f64),
    Str(String),
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
            Lit::Str(value) => Self::Str(value.clone()),
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
    pub body: ExprId,
    env: CapturedEnv,
}

#[derive(Debug, Clone, PartialEq)]
pub enum Thunk {
    Expr {
        body: ExprId,
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

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct GuardId(pub u32);

#[derive(Debug, Clone, PartialEq, Eq)]
struct ActiveFrame {
    id: GuardId,
    handler_path: Option<Vec<String>>,
    handler_key: Option<InternedPath>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum ValueMarker {
    Frame { id: GuardId },
    AddId(AddIdMarker),
}

impl ValueMarker {
    fn frame_id(&self) -> Option<GuardId> {
        match self {
            Self::Frame { id } => Some(*id),
            Self::AddId(_) => None,
        }
    }

    fn add_id(&self) -> Option<&AddIdMarker> {
        match self {
            Self::Frame { .. } => None,
            Self::AddId(marker) => Some(marker),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct AddIdMarker {
    pub id: GuardId,
    pub path: Vec<String>,
    path_key: InternedPath,
    pub depth: u32,
    pub guard_own_path: bool,
    pub guard_foreign_path: bool,
    pub carry_after_frame: bool,
}

#[derive(Debug, Clone, PartialEq, Default)]
pub struct CapturedEnv {
    locals: Rc<HashMap<DefId, Value>>,
}

impl CapturedEnv {
    fn get(&self, def: DefId) -> Option<&Value> {
        self.locals.get(&def)
    }

    fn insert(&mut self, def: DefId, value: Value) {
        Rc::make_mut(&mut self.locals).insert(def, value);
    }
}

#[derive(Debug, Clone, Default, PartialEq, Eq, Hash)]
struct InternedPath {
    segments: Rc<[u32]>,
}

impl InternedPath {
    fn from_segments(segments: Vec<u32>) -> Self {
        Self {
            segments: Rc::from(segments),
        }
    }

    fn segments(&self) -> &[u32] {
        &self.segments
    }
}

#[derive(Debug, Default)]
struct PathInterner {
    segments: HashMap<String, u32>,
    next_segment: u32,
}

impl PathInterner {
    fn intern(&mut self, path: &[String]) -> InternedPath {
        let segments = path
            .iter()
            .map(|segment| self.intern_segment(segment))
            .collect();
        InternedPath::from_segments(segments)
    }

    fn intern_segment(&mut self, segment: &str) -> u32 {
        if let Some(id) = self.segments.get(segment) {
            return *id;
        }
        let id = self.next_segment;
        self.next_segment += 1;
        self.segments.insert(segment.to_string(), id);
        id
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct ContinuationId(pub u32);

#[derive(Debug, Clone, PartialEq)]
pub enum RuntimeError {
    MissingExpr {
        expr: ExprId,
    },
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
            Self::MissingExpr { expr } => write!(f, "missing control expression e{}", expr.0),
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
    path_key: InternedPath,
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
    path_key: InternedPath,
    guard_ids: Vec<GuardId>,
    carried_guard_ids: Vec<GuardId>,
    payload: Value,
    resume: BindResume<'a>,
}

fn value_result<'a>(value: Value) -> RuntimeResult<'a> {
    Ok(EvalResult::Value(value))
}

fn bind_done<'a>(matched: bool, env: CapturedEnv) -> BindResult<'a> {
    Ok(BindEvalResult::Done { matched, env })
}

fn pattern_observes_value(pat: &Pat) -> bool {
    match pat {
        Pat::Wild | Pat::Var(_) => false,
        Pat::As(pat, _) => pattern_observes_value(pat),
        Pat::Lit(_)
        | Pat::Tuple(_)
        | Pat::List { .. }
        | Pat::Record { .. }
        | Pat::PolyVariant(_, _)
        | Pat::Con(_, _)
        | Pat::Ref(_)
        | Pat::Or(_, _) => true,
    }
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
        PrimitiveOp::StringConcat => Ok(Value::Str(format!(
            "{}{}",
            expect_str(&args[0])?,
            expect_str(&args[1])?
        ))),
        PrimitiveOp::StringLen => Ok(Value::Int(expect_str(&args[0])?.chars().count() as i64)),
        PrimitiveOp::StringIndex => {
            let text = expect_str(&args[0])?;
            let index =
                usize::try_from(expect_int(&args[1])?).map_err(|_| RuntimeError::ExpectedInt {
                    value: args[1].clone(),
                })?;
            text.chars()
                .nth(index)
                .map(|ch| Value::Str(ch.to_string()))
                .ok_or_else(|| RuntimeError::UnsupportedPrimitive { op })
        }
        PrimitiveOp::StringIndexRangeRaw => {
            let text = expect_str(&args[0])?;
            let start =
                usize::try_from(expect_int(&args[1])?).map_err(|_| RuntimeError::ExpectedInt {
                    value: args[1].clone(),
                })?;
            let end =
                usize::try_from(expect_int(&args[2])?).map_err(|_| RuntimeError::ExpectedInt {
                    value: args[2].clone(),
                })?;
            Ok(Value::Str(
                text.chars().skip(start).take(end - start).collect(),
            ))
        }
        PrimitiveOp::StringSpliceRaw => {
            let text = expect_str(&args[0])?;
            let start =
                usize::try_from(expect_int(&args[1])?).map_err(|_| RuntimeError::ExpectedInt {
                    value: args[1].clone(),
                })?;
            let end =
                usize::try_from(expect_int(&args[2])?).map_err(|_| RuntimeError::ExpectedInt {
                    value: args[2].clone(),
                })?;
            let insert = expect_str(&args[3])?;
            let prefix = text.chars().take(start).collect::<String>();
            let suffix = text.chars().skip(end).collect::<String>();
            Ok(Value::Str(format!("{prefix}{insert}{suffix}")))
        }
        PrimitiveOp::IntToString => Ok(Value::Str(expect_int(&args[0])?.to_string())),
        PrimitiveOp::IntToHex => Ok(Value::Str(format!("{:x}", expect_int(&args[0])?))),
        PrimitiveOp::IntToUpperHex => Ok(Value::Str(format!("{:X}", expect_int(&args[0])?))),
        PrimitiveOp::IntToFloat => Ok(Value::Float(expect_int(&args[0])? as f64)),
        PrimitiveOp::FloatToString => Ok(Value::Str(format_float(expect_float(&args[0])?))),
        PrimitiveOp::BoolToString => Ok(Value::Str(expect_bool(&args[0])?.to_string())),
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
            let index =
                usize::try_from(expect_int(&args[1])?).map_err(|_| RuntimeError::ExpectedInt {
                    value: args[1].clone(),
                })?;
            expect_list(&args[0])?
                .index(index)
                .map(|value| (*value).clone())
                .ok_or_else(|| RuntimeError::ExpectedList {
                    value: args[0].clone(),
                })
        }
        PrimitiveOp::ListIndexRangeRaw => {
            let start =
                usize::try_from(expect_int(&args[1])?).map_err(|_| RuntimeError::ExpectedInt {
                    value: args[1].clone(),
                })?;
            let end =
                usize::try_from(expect_int(&args[2])?).map_err(|_| RuntimeError::ExpectedInt {
                    value: args[2].clone(),
                })?;
            expect_list(&args[0])?
                .index_range(start, end)
                .map(Value::List)
                .ok_or_else(|| RuntimeError::ExpectedList {
                    value: args[0].clone(),
                })
        }
        PrimitiveOp::ListSpliceRaw => {
            let start =
                usize::try_from(expect_int(&args[1])?).map_err(|_| RuntimeError::ExpectedInt {
                    value: args[1].clone(),
                })?;
            let end =
                usize::try_from(expect_int(&args[2])?).map_err(|_| RuntimeError::ExpectedInt {
                    value: args[2].clone(),
                })?;
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
        PrimitiveOp::CharToString => Ok(Value::Str(expect_str(&args[0])?.to_string())),
        PrimitiveOp::CharIsWhitespace => Ok(Value::Bool(expect_str(&args[0])?.trim().is_empty())),
        PrimitiveOp::CharIsPunctuation => Ok(Value::Bool(
            expect_str(&args[0])?
                .chars()
                .all(|ch| ch.is_ascii_punctuation()),
        )),
        PrimitiveOp::CharIsWord => Ok(Value::Bool(
            expect_str(&args[0])?
                .chars()
                .all(|ch| ch == '_' || ch.is_alphanumeric()),
        )),
        PrimitiveOp::ListIndexRange
        | PrimitiveOp::ListSplice
        | PrimitiveOp::StringIndexRange
        | PrimitiveOp::StringSplice
        | PrimitiveOp::StringLineCount
        | PrimitiveOp::StringLineRange
        | PrimitiveOp::StringToBytes
        | PrimitiveOp::BytesLen
        | PrimitiveOp::BytesEq
        | PrimitiveOp::BytesConcat
        | PrimitiveOp::BytesIndex
        | PrimitiveOp::BytesIndexRange
        | PrimitiveOp::BytesToUtf8Raw
        | PrimitiveOp::BytesToPath
        | PrimitiveOp::PathToBytes => Err(RuntimeError::UnsupportedPrimitive { op }),
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
            def: DefId(constructors.empty.0),
            payloads: Vec::new(),
        }),
        ListView::Leaf(value) => Ok(Value::DataConstructor {
            def: DefId(constructors.leaf.0),
            payloads: vec![(*value).clone()],
        }),
        ListView::Node { left, right, .. } => Ok(Value::DataConstructor {
            def: DefId(constructors.node.0),
            payloads: vec![Value::List(left), Value::List(right)],
        }),
    }
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

fn expect_str(value: &Value) -> Result<&str, RuntimeError> {
    let (value, _) = value_view(value);
    match value {
        Value::Str(value) => Ok(value),
        value => Err(RuntimeError::UnsupportedBoundary {
            feature: format!("expected str, got {value:?}"),
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

fn expect_eval_value(result: EvalResult<'_>) -> Result<Value, RuntimeError> {
    match result {
        EvalResult::Value(value) => Ok(value),
        EvalResult::Request(request) => Err(RuntimeError::UnhandledEffect { path: request.path }),
    }
}

fn is_ref_update_request(path: &[String]) -> bool {
    path == ["std", "control", "var", "ref_update", "update"]
}

fn value_equivalent(left: &Value, right: &Value) -> bool {
    let (left, _) = value_view(left);
    let (right, _) = value_view(right);
    match (left, right) {
        (Value::Int(left), Value::Int(right)) => left == right,
        (Value::BigInt(left), Value::BigInt(right)) => left == right,
        (Value::Float(left), Value::Float(right)) => left == right,
        (Value::Str(left), Value::Str(right)) => left == right,
        (Value::Bool(left), Value::Bool(right)) => left == right,
        (Value::Unit, Value::Unit) => true,
        (Value::Tuple(left), Value::Tuple(right)) => {
            left.len() == right.len()
                && left
                    .iter()
                    .zip(right)
                    .all(|(left, right)| value_equivalent(left, right))
        }
        (
            Value::PolyVariant {
                tag: left_tag,
                payloads: left_payloads,
            },
            Value::PolyVariant {
                tag: right_tag,
                payloads: right_payloads,
            },
        ) => {
            left_tag == right_tag
                && left_payloads.len() == right_payloads.len()
                && left_payloads
                    .iter()
                    .zip(right_payloads)
                    .all(|(left, right)| value_equivalent(left, right))
        }
        (Value::Record(left), Value::Record(right)) => {
            left.len() == right.len()
                && left.iter().zip(right).all(|(left, right)| {
                    left.name == right.name && value_equivalent(&left.value, &right.value)
                })
        }
        _ => false,
    }
}

fn find_record_field<'a>(fields: &'a [ValueField], name: &str) -> Option<(usize, &'a ValueField)> {
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

fn stack_handler_markers(
    id: GuardId,
    path: Vec<String>,
    path_key: InternedPath,
) -> Vec<ValueMarker> {
    vec![
        ValueMarker::Frame { id },
        ValueMarker::AddId(AddIdMarker {
            id,
            path: path.clone(),
            path_key: path_key.clone(),
            depth: 0,
            guard_own_path: false,
            guard_foreign_path: true,
            carry_after_frame: false,
        }),
        ValueMarker::AddId(AddIdMarker {
            id,
            path,
            path_key,
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
    if markers.is_empty() || is_scalar_value(&value) {
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

fn counted_path_has_prefix(
    stats: &mut RuntimeStats,
    path: &InternedPath,
    prefix: &InternedPath,
) -> bool {
    stats.path_prefix_checks += 1;
    if prefix.segments().len() > path.segments().len() {
        return false;
    }
    for (segment, prefix) in path.segments().iter().zip(prefix.segments()) {
        stats.path_prefix_segments += 1;
        if segment != prefix {
            return false;
        }
    }
    true
}

fn counted_path_eq(stats: &mut RuntimeStats, left: &InternedPath, right: &InternedPath) -> bool {
    stats.path_eq_checks += 1;
    if left.segments().len() != right.segments().len() {
        return false;
    }
    for (left, right) in left.segments().iter().zip(right.segments()) {
        stats.path_eq_segments += 1;
        if left != right {
            return false;
        }
    }
    true
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
            | Value::Bool(_)
            | Value::Unit
    )
}
