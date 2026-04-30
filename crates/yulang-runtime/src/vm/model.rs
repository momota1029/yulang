use super::*;

#[derive(Debug, Clone, PartialEq)]
pub enum VmResult {
    Value(VmValue),
    Request(VmRequest),
}

#[derive(Debug, Clone, PartialEq)]
pub enum VmValue {
    Int(String),
    Float(String),
    String(StringTree),
    Bool(bool),
    Unit,
    List(ListTree<VmValue>),
    Tuple(Vec<VmValue>),
    Record(BTreeMap<core_ir::Name, VmValue>),
    Variant {
        tag: core_ir::Name,
        value: Option<Box<VmValue>>,
    },
    EffectOp(core_ir::Path),
    PrimitiveOp(Rc<VmPrimitive>),
    Resume(Rc<VmResume>),
    Closure(Rc<VmClosure>),
    Thunk(Rc<VmThunk>),
    EffectId(u64),
}

#[derive(Debug, Clone, PartialEq)]
pub struct VmRequest {
    pub effect: core_ir::Path,
    pub payload: VmValue,
    pub continuation: VmContinuation,
    pub blocked_id: Option<u64>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct VmPrimitive {
    pub op: core_ir::PrimitiveOp,
    pub args: Vec<VmValue>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct VmClosure {
    pub(super) param: core_ir::Name,
    pub(super) param_ty: Type,
    pub(super) body: Expr,
    pub(super) ret: Type,
    pub(super) env: Env,
    pub(super) self_name: Option<core_ir::Path>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct VmThunk {
    pub(super) body: ThunkBody,
    pub(super) env: Env,
    pub(super) guard_stack: GuardStack,
    pub(super) blocked: Vec<BlockedEffect>,
}

#[derive(Debug, Clone, PartialEq)]
pub(super) enum ThunkBody {
    Value(VmValue),
    Expr(Expr),
    Emit {
        effect: core_ir::Path,
        payload: VmValue,
    },
}

#[derive(Debug, Clone, PartialEq)]
pub struct VmResume {
    pub(super) continuation: VmContinuation,
}

#[derive(Debug, Clone, PartialEq, Default)]
pub struct VmContinuation {
    pub(super) frames: Vec<Frame>,
    pub(super) guard_stack: GuardStack,
}

#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub(super) struct GuardStack(pub(super) PersistentVector<GuardEntry>);

#[derive(Debug, Clone, PartialEq, Eq)]
pub(super) struct PersistentVector<T> {
    pub(super) len: usize,
    pub(super) tail: Option<Rc<PersistentVectorChunk<T>>>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) struct GuardEntry {
    pub(super) var: EffectIdVar,
    pub(super) id: u64,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(super) struct PersistentVectorChunk<T> {
    pub(super) items: Rc<[T]>,
    pub(super) parent: Option<Rc<PersistentVectorChunk<T>>>,
}

#[derive(Debug, Clone, PartialEq)]
pub(super) struct BlockedEffect {
    pub(super) guard_id: u64,
    pub(super) allowed: core_ir::Type,
}

#[derive(Debug, Clone, PartialEq)]
pub(super) enum Frame {
    BindHere,
    ApplyCallee {
        arg: Expr,
        env: Env,
        delay_arg: bool,
    },
    ApplyArg {
        callee: VmValue,
    },
    If {
        then_branch: Expr,
        else_branch: Expr,
        env: Env,
    },
    Tuple {
        done: Vec<VmValue>,
        remaining: Vec<Expr>,
        env: Env,
    },
    Select {
        field: core_ir::Name,
    },
    Match {
        arms: Vec<MatchArm>,
        env: Env,
    },
    BlockLet {
        pattern: Pattern,
        remaining: Vec<Stmt>,
        tail: Option<Expr>,
        env: Env,
    },
    BlockExpr {
        remaining: Vec<Stmt>,
        tail: Option<Expr>,
        env: Env,
    },
    Handle {
        id: u64,
        arms: Vec<HandleArm>,
        env: Env,
        guard_stack: GuardStack,
    },
    HandleGuard {
        id: u64,
        request: VmRequest,
        outer: VmContinuation,
        handler_guard_stack: GuardStack,
        arms: Vec<HandleArm>,
        env: Env,
        arm_env: Env,
        body: Expr,
    },
    LocalPushId {
        parent: GuardStack,
    },
    Coerce {
        to: core_ir::Type,
    },
    WrapThunkResult {
        expected_ty: Type,
    },
}

pub(super) type Env = HashMap<core_ir::Path, VmValue>;
