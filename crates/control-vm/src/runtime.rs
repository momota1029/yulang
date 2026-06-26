//! Runtime for the lowered control IR.

use std::collections::{HashMap, HashSet, VecDeque};
use std::fmt;
use std::rc::Rc;

use list_tree::{ListTree, ListView};
use mono::{FunctionAdapterHygiene, Lit, PrimitiveContext, PrimitiveOp, RangeConstructors, Type};
use num_bigint::BigInt;
use smallvec::SmallVec;
use text_tree::{BytesTree, StringTree};

use crate::boundary::{
    equivalent_runtime_types, function_parts, thunk_value_type, value_boundary_supported,
};
use crate::ir::{
    CaseArm, DefId, Expr, ExprId, InstanceId, Pat, Program, RecordPatField, RecordSpread, Root,
    SelectResolution, Stmt,
};
use crate::lower::{LowerError, lower};
use crate::validate::{ValidateError, validate};

mod bind;
mod engine;
mod eval;
mod flow;
mod frame;
mod scope_state;
mod thunk;
mod time;

use engine::Runtime;
use frame::{
    BindThen, Continuation, ContinuationMarkerScope, Frame, RefSetFinish, RefSetResumeMode,
    prepend_marker_scope, push_frame,
};
use scope_state::{ScopeRequestMarking, ScopeState};
use time::{Duration, Instant};

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
    run_program_with_host_stats_and_timings(program, host).map(|(values, stats, _)| (values, stats))
}

pub fn run_program_with_host_stats_and_timings<F>(
    program: &Program,
    host: &mut F,
) -> Result<(Vec<Value>, RuntimeStats, RuntimeTimings), RunError>
where
    F: FnMut(&[String], &Value) -> Option<Value>,
{
    let validate_start = Instant::now();
    validate(program).map_err(RunError::Validate)?;
    let validate = validate_start.elapsed();

    let init_start = Instant::now();
    let mut runtime = Runtime::new(program);
    let init = init_start.elapsed();

    let execute_start = Instant::now();
    let values = runtime.run_with_host(host).map_err(RunError::Runtime)?;
    let execute = execute_start.elapsed();

    Ok((
        values,
        runtime.stats,
        RuntimeTimings {
            validate,
            init,
            execute,
        },
    ))
}

#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct RuntimeStats {
    pub expr_evals: u64,
    /// Full `Expr` clones performed by eval. This should stay at zero on the dispatch path.
    pub expr_clones: u64,
    pub env_lookups: u64,
    pub env_lookup_hits: u64,
    pub env_lookup_misses: u64,
    pub env_lookup_steps: u64,
    pub env_inserts: u64,
    pub env_cow_clones: u64,
    pub env_cow_entries_copied: u64,
    pub env_max_size: u64,
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
    pub continuation_capture_clones: u64,
    pub continuation_invoke_clones: u64,
    pub continuation_frames_cloned: u64,
    pub continuation_marker_scopes_cloned: u64,
    pub shared_frame_unwrap_clones: u64,
    pub shared_frame_unwrap_apply_clones: u64,
    pub shared_frame_unwrap_direct_clones: u64,
    pub shared_frame_unwrap_data_clones: u64,
    pub shared_frame_unwrap_case_clones: u64,
    pub shared_frame_unwrap_catch_clones: u64,
    pub shared_frame_unwrap_block_clones: u64,
    pub shared_frame_unwrap_bind_clones: u64,
    pub shared_frame_unwrap_refset_clones: u64,
    pub frame_allocs: u64,
    pub max_continuation_frames: u64,
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
    pub marker_scope_frame_touches: u64,
    pub marker_scope_consume_calls: u64,
    pub marker_scope_consume_nonempty_calls: u64,
    pub marker_scope_consume_touches: u64,
    pub marker_scope_close_calls: u64,
    pub marker_scope_close_pops: u64,
    pub marker_scope_request_closes: u64,
    pub marker_scope_extend_touches: u64,
    pub marker_scope_request_close_touches: u64,
    pub marker_scope_max_depth: u64,
    pub instance_eval_calls: u64,
    pub instance_cache_hits: u64,
    pub instance_cache_misses: u64,
    pub path_prefix_checks: u64,
    pub path_prefix_segments: u64,
    pub path_eq_checks: u64,
    pub path_eq_segments: u64,
    pub active_add_id_scans: u64,
    pub active_frame_scans: u64,
    pub scope_state_shadow_checks: u64,
    pub scope_state_shadow_active_add_markers: u64,
    pub scope_state_shadow_path_candidates: u64,
    pub scope_state_shadow_all_path_candidates: u64,
    pub scope_state_shadow_own_path_candidates: u64,
    pub scope_state_shadow_foreign_path_candidates: u64,
}

#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct RuntimeTimings {
    pub validate: Duration,
    pub init: Duration,
    pub execute: Duration,
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
    Str(StringTree),
    Bytes(BytesTree),
    Bool(bool),
    Unit,
    Tuple(SharedValues),
    List(ListTree<Rc<Value>>),
    Record(SharedValueFields),
    PolyVariant {
        tag: String,
        payloads: SharedValues,
    },
    DataConstructor {
        def: DefId,
        payloads: SharedValues,
    },
    ConstructorFunction(ConstructorFunction),
    PrimitiveOp(PrimitiveValue),
    Closure(Rc<Closure>),
    RecursiveClosure {
        def: DefId,
        closure: Rc<Closure>,
    },
    Thunk(Rc<Thunk>),
    FunctionAdapter(Rc<FunctionAdapter>),
    EffectOp {
        path: Vec<String>,
        path_key: InternedPath,
    },
    Continuation(ContinuationId),
    Marked {
        value: Box<Value>,
        markers: SharedMarkers,
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
        path_key: InternedPath,
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
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct ActiveHandlerFrame {
    frame_index: usize,
    id: GuardId,
    handler_key: InternedPathPrefix,
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct ActiveAddIdMarker {
    marker: AddIdMarker,
    entry_frame_len: usize,
}

#[derive(Debug, Clone, Copy)]
struct MarkerCheckpoint {
    guard_len: usize,
    frame_len: usize,
    handler_frame_len: usize,
    add_id_len: usize,
    plan_len: usize,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum ValueMarker {
    Frame { id: GuardId },
    AddId(AddIdMarker),
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct AddIdMarker {
    pub id: GuardId,
    path_key: InternedPathPrefix,
    pub depth: u32,
    pub guard_own_path: bool,
    pub guard_foreign_path: bool,
    pub carry_after_frame: bool,
    pub preserve_own_on_resume: bool,
}

#[derive(Debug, Clone, PartialEq, Default)]
pub struct CapturedEnv {
    frame: Option<Rc<EnvFrame>>,
}

#[derive(Debug, Clone, PartialEq)]
struct EnvFrame {
    parent: Option<Rc<EnvFrame>>,
    def: DefId,
    value: Value,
    depth: usize,
}

struct EnvLookup<'a> {
    value: Option<&'a Value>,
    steps: usize,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct EnvInsertStats {
    cow_cloned: bool,
    entries_copied: usize,
    new_size: usize,
}

impl CapturedEnv {
    fn get(&self, def: DefId) -> EnvLookup<'_> {
        let mut steps = 0;
        let mut frame = self.frame.as_deref();
        while let Some(current) = frame {
            steps += 1;
            if current.def == def {
                return EnvLookup {
                    value: Some(&current.value),
                    steps,
                };
            }
            frame = current.parent.as_deref();
        }
        EnvLookup { value: None, steps }
    }

    fn insert(&mut self, def: DefId, value: Value) -> EnvInsertStats {
        let parent = self.frame.take();
        let depth = parent.as_ref().map_or(1, |frame| frame.depth + 1);
        self.frame = Some(Rc::new(EnvFrame {
            parent,
            def,
            value,
            depth,
        }));
        EnvInsertStats {
            cow_cloned: false,
            entries_copied: 0,
            new_size: depth,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct InternedPath {
    id: u32,
    len: usize,
    prefix_ids: Rc<[u32]>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
struct InternedPathPrefix {
    id: u32,
    len: usize,
}

impl InternedPath {
    fn prefix(&self) -> InternedPathPrefix {
        InternedPathPrefix {
            id: self.id,
            len: self.len,
        }
    }

    fn has_prefix(&self, prefix: InternedPathPrefix) -> bool {
        if prefix.len == 0 {
            return true;
        }
        self.prefix_ids
            .get(prefix.len - 1)
            .is_some_and(|prefix_id| *prefix_id == prefix.id)
    }
}

#[derive(Debug, Default)]
struct PathInterner {
    segments: HashMap<String, u32>,
    paths: HashMap<Vec<u32>, u32>,
    entries: Vec<InternedPathEntry>,
    next_segment: u32,
}

impl PathInterner {
    fn intern(&mut self, path: &[String]) -> InternedPath {
        let segments = path
            .iter()
            .map(|segment| self.intern_segment(segment))
            .collect::<Vec<_>>();
        self.intern_segments(&segments)
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

    fn intern_segments(&mut self, segments: &[u32]) -> InternedPath {
        if let Some(id) = self.paths.get(segments) {
            return self.entries[*id as usize].to_path(*id);
        }

        let mut prefix_ids = Vec::with_capacity(segments.len());
        for len in 1..segments.len() {
            prefix_ids.push(self.intern_segments(&segments[..len]).id);
        }

        let id = self.entries.len() as u32;
        prefix_ids.push(id);

        let entry = InternedPathEntry {
            len: segments.len(),
            prefix_ids: Rc::from(prefix_ids),
        };
        self.paths.insert(segments.to_vec(), id);
        self.entries.push(entry);
        self.entries[id as usize].to_path(id)
    }
}

#[derive(Debug)]
struct InternedPathEntry {
    len: usize,
    prefix_ids: Rc<[u32]>,
}

impl InternedPathEntry {
    fn to_path(&self, id: u32) -> InternedPath {
        InternedPath {
            id,
            len: self.len,
            prefix_ids: self.prefix_ids.clone(),
        }
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

type RuntimeResult = Result<EvalResult, RuntimeError>;
type RuntimeBlockStmts = Rc<[Stmt]>;
type RuntimeCaseArms = Rc<[CaseArm]>;
type RuntimeCatchArms = Rc<[RuntimeCatchArm]>;
type SharedFrame = Rc<Frame>;
type SharedValues = Rc<[Value]>;
type SharedValueFields = Rc<[ValueField]>;
type SharedMarkerScopes = Rc<[ContinuationMarkerScope]>;
type SharedMarkers = Rc<[ValueMarker]>;

enum EvalResult {
    Value(Value),
    Request(Request),
}

#[derive(Clone)]
struct Request {
    path: Vec<String>,
    path_key: InternedPath,
    guard_ids: GuardIds,
    carried_guards: Vec<CarriedGuard>,
    handler_boundary: Option<HandlerBoundary>,
    payload: Value,
    continuation: Continuation,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum GuardSkip {
    Preserve(GuardId),
}

impl GuardSkip {
    fn apply(self, request: Request) -> Request {
        match self {
            GuardSkip::Preserve(_) => request,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct CarriedGuard {
    id: GuardId,
    entry_frame_len: usize,
    exposed_guard_ids: GuardIds,
}

#[derive(Debug, Clone, Default, PartialEq, Eq)]
struct GuardIds {
    ids: SmallVec<[GuardId; 4]>,
}

impl GuardIds {
    fn new() -> Self {
        Self {
            ids: SmallVec::new(),
        }
    }

    fn is_empty(&self) -> bool {
        self.ids.is_empty()
    }

    fn contains(&self, id: GuardId) -> bool {
        self.ids.contains(&id)
    }

    fn push_unique(&mut self, id: GuardId) -> bool {
        if self.contains(id) {
            return false;
        }
        self.ids.push(id);
        true
    }

    fn iter(&self) -> impl Iterator<Item = &GuardId> {
        self.ids.iter()
    }
}

impl From<Vec<GuardId>> for GuardIds {
    fn from(ids: Vec<GuardId>) -> Self {
        let mut guard_ids = Self::new();
        for id in ids {
            guard_ids.push_unique(id);
        }
        guard_ids
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct HandlerBoundary {
    id: GuardId,
    handler_key: InternedPathPrefix,
    blocked: bool,
}

#[derive(Clone)]
struct RuntimeCatchArm {
    operation_key: Option<InternedPath>,
    pat: Pat,
    continuation: Option<Pat>,
    guard: Option<ExprId>,
    body: ExprId,
}

#[derive(Clone)]
struct RuntimeBlock {
    stmts: RuntimeBlockStmts,
    tail: Option<ExprId>,
}

fn value_result(value: Value) -> RuntimeResult {
    Ok(EvalResult::Value(value))
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
            payloads: shared_values(args),
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
                Ok(text) => Ok(Value::Tuple(shared_values(vec![
                    Value::Str(StringTree::from(text)),
                    Value::Int(bytes.len() as i64),
                ]))),
                Err(error) => {
                    let valid = error.valid_up_to();
                    let text = std::str::from_utf8(&bytes[..valid]).unwrap_or("");
                    Ok(Value::Tuple(shared_values(vec![
                        Value::Str(StringTree::from(text)),
                        Value::Int(valid as i64),
                    ])))
                }
            }
        }
        PrimitiveOp::BytesToPath | PrimitiveOp::PathToBytes => {
            Err(RuntimeError::UnsupportedPrimitive { op })
        }
    }
}

fn finish_ref_set_values(finish: RefSetFinish, values: Vec<Value>) -> Value {
    match finish {
        RefSetFinish::Tuple => Value::Tuple(shared_values(values)),
        RefSetFinish::List => Value::List(ListTree::from_items(values.into_iter().map(Rc::new))),
        RefSetFinish::PolyVariant { tag } => Value::PolyVariant {
            tag,
            payloads: shared_values(values),
        },
        RefSetFinish::DataConstructor { def } => Value::DataConstructor {
            def,
            payloads: shared_values(values),
        },
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
            payloads: shared_values(Vec::new()),
        }),
        ListView::Leaf(value) => Ok(Value::DataConstructor {
            def: DefId(constructors.leaf.0),
            payloads: shared_values(vec![(*value).clone()]),
        }),
        ListView::Node { left, right, .. } => Ok(Value::DataConstructor {
            def: DefId(constructors.node.0),
            payloads: shared_values(vec![Value::List(left), Value::List(right)]),
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
        def: DefId(constructors.included.0),
        payloads: shared_values(vec![Value::Int(index_to_int(start)?)]),
    };
    let end = Value::DataConstructor {
        def: DefId(constructors.excluded.0),
        payloads: shared_values(vec![Value::Int(index_to_int(end)?)]),
    };
    Ok(Value::DataConstructor {
        def: DefId(constructors.within.0),
        payloads: shared_values(vec![start, end]),
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
    if *def != DefId(constructors.within.0) {
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
            match bounds.as_ref() {
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
    if *def == DefId(constructors.unbounded.0) {
        return Ok(0);
    }
    if *def == DefId(constructors.included.0) {
        return single_index_payload(payloads);
    }
    if *def == DefId(constructors.excluded.0) {
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
    if *def == DefId(constructors.unbounded.0) {
        return Ok(len);
    }
    if *def == DefId(constructors.included.0) {
        return single_index_payload(payloads)?
            .checked_add(1)
            .ok_or_else(|| RuntimeError::UnsupportedBoundary {
                feature: "range end bound overflow".to_string(),
            });
    }
    if *def == DefId(constructors.excluded.0) {
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

fn expect_eval_value(result: EvalResult) -> Result<Value, RuntimeError> {
    match result {
        EvalResult::Value(value) => Ok(value),
        EvalResult::Request(request) => Err(RuntimeError::UnhandledEffect { path: request.path }),
    }
}

fn ref_update_update_path() -> Vec<String> {
    ["std", "control", "var", "ref_update", "update"]
        .into_iter()
        .map(str::to_string)
        .collect()
}

fn value_equivalent(left: &Value, right: &Value) -> bool {
    let (left, _) = value_view(left);
    let (right, _) = value_view(right);
    match (left, right) {
        (Value::Int(left), Value::Int(right)) => left == right,
        (Value::BigInt(left), Value::BigInt(right)) => left == right,
        (Value::Float(left), Value::Float(right)) => left == right,
        (Value::Str(left), Value::Str(right)) => left == right,
        (Value::Bytes(left), Value::Bytes(right)) => left == right,
        (Value::Bool(left), Value::Bool(right)) => left == right,
        (Value::Unit, Value::Unit) => true,
        (Value::Tuple(left), Value::Tuple(right)) => {
            left.len() == right.len()
                && left
                    .iter()
                    .zip(right.iter())
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
                    .zip(right_payloads.iter())
                    .all(|(left, right)| value_equivalent(left, right))
        }
        (Value::Record(left), Value::Record(right)) => {
            left.len() == right.len()
                && left.iter().zip(right.iter()).all(|(left, right)| {
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

fn markers_for_function_call(markers: &[ValueMarker]) -> Vec<ValueMarker> {
    dedupe_markers(
        markers
            .iter()
            .cloned()
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

fn shared_markers_for_function_call(markers: &SharedMarkers) -> SharedMarkers {
    if markers_for_function_call_is_identity(markers) {
        return markers.clone();
    }
    shared_markers(markers_for_function_call(markers))
}

fn markers_for_function_call_is_identity(markers: &[ValueMarker]) -> bool {
    for (index, marker) in markers.iter().enumerate() {
        if matches!(marker, ValueMarker::AddId(marker) if marker.depth != 0) {
            return false;
        }
        if markers[..index].iter().any(|existing| existing == marker) {
            return false;
        }
    }
    true
}

fn markers_for_continuation_call(markers: &[ValueMarker]) -> Vec<ValueMarker> {
    dedupe_markers(
        markers
            .iter()
            .cloned()
            .map(|marker| match marker {
                ValueMarker::Frame { id } => ValueMarker::Frame { id },
                ValueMarker::AddId(marker) => ValueMarker::AddId(AddIdMarker {
                    depth: marker.depth.saturating_sub(1),
                    guard_own_path: marker.guard_own_path && marker.preserve_own_on_resume,
                    guard_foreign_path: true,
                    ..marker
                }),
            })
            .collect(),
    )
}

fn shared_markers_for_continuation_call(markers: &SharedMarkers) -> SharedMarkers {
    if markers_for_continuation_call_is_identity(markers) {
        return markers.clone();
    }
    shared_markers(markers_for_continuation_call(markers))
}

fn markers_for_continuation_call_is_identity(markers: &[ValueMarker]) -> bool {
    for (index, marker) in markers.iter().enumerate() {
        if let ValueMarker::AddId(marker) = marker
            && (marker.depth != 0
                || (marker.guard_own_path && !marker.preserve_own_on_resume)
                || !marker.guard_foreign_path)
        {
            return false;
        }
        if markers[..index].iter().any(|existing| existing == marker) {
            return false;
        }
    }
    true
}

fn markers_for_continuation_resume(markers: &[ValueMarker]) -> Vec<ValueMarker> {
    dedupe_markers(
        markers
            .iter()
            .cloned()
            .map(|marker| match marker {
                ValueMarker::AddId(marker) => ValueMarker::AddId(AddIdMarker {
                    guard_own_path: marker.guard_own_path && marker.preserve_own_on_resume,
                    guard_foreign_path: true,
                    ..marker
                }),
                marker => marker,
            })
            .collect(),
    )
}

fn shared_markers_for_continuation_resume(markers: &SharedMarkers) -> SharedMarkers {
    if markers_for_continuation_resume_is_identity(markers) {
        return markers.clone();
    }
    shared_markers(markers_for_continuation_resume(markers))
}

fn markers_for_continuation_resume_is_identity(markers: &[ValueMarker]) -> bool {
    for (index, marker) in markers.iter().enumerate() {
        if let ValueMarker::AddId(marker) = marker
            && ((marker.guard_own_path && !marker.preserve_own_on_resume)
                || !marker.guard_foreign_path)
        {
            return false;
        }
        if markers[..index].iter().any(|existing| existing == marker) {
            return false;
        }
    }
    true
}

fn shared_markers(markers: Vec<ValueMarker>) -> SharedMarkers {
    Rc::from(markers)
}

fn shared_combined_markers(left: &SharedMarkers, right: &SharedMarkers) -> SharedMarkers {
    if left.is_empty() {
        return right.clone();
    }
    if right.is_empty() || markers_contain_all(left, right) {
        return left.clone();
    }
    let mut markers = left.to_vec();
    extend_marker_list(&mut markers, right);
    shared_markers(markers)
}

fn shared_values(values: Vec<Value>) -> SharedValues {
    Rc::from(values.into_boxed_slice())
}

fn shared_value_fields(fields: Vec<ValueField>) -> SharedValueFields {
    Rc::from(fields.into_boxed_slice())
}

fn shared_block_stmts(stmts: &[Stmt]) -> RuntimeBlockStmts {
    Rc::from(stmts.to_vec().into_boxed_slice())
}

fn shared_case_arms(arms: &[CaseArm]) -> RuntimeCaseArms {
    Rc::from(arms.to_vec().into_boxed_slice())
}

fn stack_handler_markers(id: GuardId, path_key: InternedPath) -> Vec<ValueMarker> {
    let path_key = path_key.prefix();
    vec![
        ValueMarker::Frame { id },
        ValueMarker::AddId(AddIdMarker {
            id,
            path_key,
            depth: 0,
            guard_own_path: false,
            guard_foreign_path: true,
            carry_after_frame: false,
            preserve_own_on_resume: false,
        }),
        ValueMarker::AddId(AddIdMarker {
            id,
            path_key,
            depth: 1,
            guard_own_path: true,
            guard_foreign_path: true,
            carry_after_frame: false,
            preserve_own_on_resume: false,
        }),
    ]
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
        markers: shared_markers(value_markers),
    }
}

fn mark_value_shared(value: Value, markers: &SharedMarkers) -> Value {
    if markers.is_empty() || is_scalar_value(&value) {
        return value;
    }
    match value {
        Value::Marked {
            value,
            markers: value_markers,
        } if markers_contain_all(&value_markers, markers) => Value::Marked {
            value,
            markers: value_markers,
        },
        Value::Marked { .. } => mark_value(value, markers),
        value => Value::Marked {
            value: Box::new(value),
            markers: markers.clone(),
        },
    }
}

fn markers_contain_all(existing: &[ValueMarker], required: &[ValueMarker]) -> bool {
    required
        .iter()
        .all(|marker| existing.iter().any(|existing| existing == marker))
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

fn callee_apply_closes_without_frame(value: &Value) -> bool {
    matches!(
        value,
        Value::PrimitiveOp(_)
            | Value::ConstructorFunction(_)
            | Value::EffectOp { .. }
            | Value::Continuation(_)
    )
}

fn counted_path_has_prefix(
    stats: &mut RuntimeStats,
    path: &InternedPath,
    prefix: InternedPathPrefix,
) -> bool {
    stats.path_prefix_checks += 1;
    path.has_prefix(prefix)
}

fn counted_path_eq(stats: &mut RuntimeStats, left: &InternedPath, right: &InternedPath) -> bool {
    stats.path_eq_checks += 1;
    left.id == right.id
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
            | Value::PrimitiveOp(_)
    )
}
