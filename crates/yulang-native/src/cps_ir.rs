use yulang_typed_ir as typed_ir;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CpsModule {
    pub functions: Vec<CpsFunction>,
    pub roots: Vec<CpsFunction>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CpsFunction {
    pub name: String,
    pub params: Vec<CpsValueId>,
    pub entry: CpsContinuationId,
    pub continuations: Vec<CpsContinuation>,
    pub handlers: Vec<CpsHandler>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CpsContinuation {
    pub id: CpsContinuationId,
    pub params: Vec<CpsValueId>,
    pub captures: Vec<CpsValueId>,
    pub shot_kind: CpsShotKind,
    pub stmts: Vec<CpsStmt>,
    pub terminator: CpsTerminator,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CpsShotKind {
    OneShot,
    MultiShot,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CpsStmt {
    Literal {
        dest: CpsValueId,
        literal: CpsLiteral,
    },
    FreshGuard {
        dest: CpsValueId,
        var: yulang_runtime::EffectIdVar,
    },
    PeekGuard {
        dest: CpsValueId,
    },
    FindGuard {
        dest: CpsValueId,
        guard: CpsValueId,
    },
    MakeThunk {
        dest: CpsValueId,
        entry: CpsContinuationId,
    },
    AddThunkBoundary {
        dest: CpsValueId,
        thunk: CpsValueId,
        guard: CpsValueId,
        allowed: typed_ir::Type,
        active: bool,
    },
    MakeClosure {
        dest: CpsValueId,
        entry: CpsContinuationId,
    },
    MakeRecursiveClosure {
        dest: CpsValueId,
        entry: CpsContinuationId,
    },
    ForceThunk {
        dest: CpsValueId,
        thunk: CpsValueId,
    },
    Tuple {
        dest: CpsValueId,
        items: Vec<CpsValueId>,
    },
    Record {
        dest: CpsValueId,
        base: Option<CpsValueId>,
        fields: Vec<CpsRecordField>,
    },
    RecordWithoutFields {
        dest: CpsValueId,
        base: CpsValueId,
        fields: Vec<typed_ir::Name>,
    },
    Variant {
        dest: CpsValueId,
        tag: typed_ir::Name,
        value: Option<CpsValueId>,
    },
    Select {
        dest: CpsValueId,
        base: CpsValueId,
        field: typed_ir::Name,
    },
    SelectWithDefault {
        dest: CpsValueId,
        base: CpsValueId,
        field: typed_ir::Name,
        default: CpsValueId,
    },
    RecordHasField {
        dest: CpsValueId,
        base: CpsValueId,
        field: typed_ir::Name,
    },
    TupleGet {
        dest: CpsValueId,
        tuple: CpsValueId,
        index: usize,
    },
    VariantTagEq {
        dest: CpsValueId,
        variant: CpsValueId,
        tag: typed_ir::Name,
    },
    VariantPayload {
        dest: CpsValueId,
        variant: CpsValueId,
    },
    Primitive {
        dest: CpsValueId,
        op: typed_ir::PrimitiveOp,
        args: Vec<CpsValueId>,
    },
    DirectCall {
        dest: CpsValueId,
        target: String,
        args: Vec<CpsValueId>,
        ownership: Option<CpsEffectBoundaryOwnership>,
    },
    ApplyClosure {
        dest: CpsValueId,
        closure: CpsValueId,
        arg: CpsValueId,
    },
    CloneContinuation {
        dest: CpsValueId,
        source: CpsValueId,
    },
    Resume {
        dest: CpsValueId,
        resumption: CpsValueId,
        arg: CpsValueId,
    },
    ResumeWithHandler {
        dest: CpsValueId,
        resumption: CpsValueId,
        arg: CpsValueId,
        handler: CpsHandlerId,
        envs: Vec<CpsHandlerEnv>,
    },
    InstallHandler {
        handler: CpsHandlerId,
        envs: Vec<CpsHandlerEnv>,
        /// Continuation that applies the handler's value arm when the body
        /// completes naturally. Runtime installs this as a prompt-exit frame
        /// so shallow resumptions can capture the raw body continuation
        /// without capturing the value arm.
        value: CpsContinuationId,
        /// The continuation reached when the handler scope completes —
        /// either because the body returned normally or a non-resuming
        /// arm fell through. ScopeReturn-style abort uses this as the
        /// jump target after popping the handler frame, so handler
        /// scopes can return values without bubbling past the catch.
        escape: CpsContinuationId,
    },
    UninstallHandler {
        handler: CpsHandlerId,
    },
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CpsRecordField {
    pub name: typed_ir::Name,
    pub value: CpsValueId,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CpsHandlerEnv {
    pub entry: CpsContinuationId,
    /// Value ids read at the install / reentry site.
    pub values: Vec<CpsValueId>,
    /// Value ids written into the handler arm's captured environment.
    /// Empty means `targets == values`, which keeps ordinary same-function
    /// handler installs compact.
    pub targets: Vec<CpsValueId>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CpsEffectBoundaryOwnership {
    pub owner_function: String,
    pub return_frame_resume: CpsContinuationId,
    pub force_thunk: Option<CpsValueId>,
    pub closed: bool,
    pub finite_layers: Vec<CpsEffectBoundaryFiniteLayer>,
    pub no_resume_effects: Vec<typed_ir::Path>,
    pub blocked_effects: Vec<typed_ir::Path>,
    pub open_effects: Vec<typed_ir::Path>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CpsEffectBoundaryFiniteLayer {
    pub handler: CpsHandlerId,
    pub effect: typed_ir::Path,
    pub arm_entry: CpsContinuationId,
    pub perform_function: String,
    pub perform: CpsContinuationId,
    pub perform_resume: CpsContinuationId,
    pub resume_actions: Vec<CpsEffectBoundaryResumeAction>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct CpsEffectBoundaryResumeAction {
    pub continuation: CpsContinuationId,
    pub stmt_index: usize,
    pub arg: CpsValueId,
    pub arg_literal: Option<CpsLiteral>,
    pub local_thunk_entry: Option<CpsContinuationId>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CpsEffectPerformOwnership {
    pub owner_function: String,
    pub return_frame_resume: CpsContinuationId,
    pub handler: CpsHandlerId,
    pub effect: typed_ir::Path,
    pub arm_entry: CpsContinuationId,
    pub resume_actions: Vec<CpsEffectBoundaryResumeAction>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CpsTerminator {
    Return(CpsValueId),
    Continue {
        target: CpsContinuationId,
        args: Vec<CpsValueId>,
    },
    Branch {
        cond: CpsValueId,
        then_cont: CpsContinuationId,
        else_cont: CpsContinuationId,
    },
    Perform {
        effect: typed_ir::Path,
        payload: CpsValueId,
        resume: CpsContinuationId,
        handler: CpsHandlerId,
        blocked: Option<CpsValueId>,
        ownership: Option<CpsEffectPerformOwnership>,
    },
    /// Effectful direct function call. Used inside handler scopes when the
    /// callee may perform effects. The resume continuation receives the return
    /// value; the call site's post-call computation is captured as a return
    /// frame so Perform inside the callee can include it in the resumption.
    EffectfulCall {
        target: String,
        args: Vec<CpsValueId>,
        resume: CpsContinuationId,
    },
    /// Effectful closure application. Same semantics as EffectfulCall but for
    /// first-class closures / resumptions.
    EffectfulApply {
        closure: CpsValueId,
        arg: CpsValueId,
        resume: CpsContinuationId,
    },
    /// Effectful thunk force. Used when an EffectfulCall's result is a Thunk
    /// that needs to be forced inside the handler scope — the force needs to
    /// be a terminator so its Perform captures the post-force continuation
    /// in the resumption.
    EffectfulForce {
        thunk: CpsValueId,
        resume: CpsContinuationId,
        ownership: Option<CpsEffectBoundaryOwnership>,
    },
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CpsHandler {
    pub id: CpsHandlerId,
    pub arms: Vec<CpsHandlerArm>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CpsHandlerArm {
    pub effect: typed_ir::Path,
    pub entry: CpsContinuationId,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum CpsLiteral {
    Int(String),
    Float(String),
    String(String),
    Bool(bool),
    Unit,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct CpsValueId(pub usize);

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct CpsContinuationId(pub usize);

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct CpsHandlerId(pub usize);

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct CpsHandlerContextId(pub usize);
