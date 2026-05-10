use yulang_core_ir as core_ir;

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
        fields: Vec<CpsRecordField>,
    },
    Variant {
        dest: CpsValueId,
        tag: core_ir::Name,
        value: Option<CpsValueId>,
    },
    Select {
        dest: CpsValueId,
        base: CpsValueId,
        field: core_ir::Name,
    },
    TupleGet {
        dest: CpsValueId,
        tuple: CpsValueId,
        index: usize,
    },
    VariantTagEq {
        dest: CpsValueId,
        variant: CpsValueId,
        tag: core_ir::Name,
    },
    VariantPayload {
        dest: CpsValueId,
        variant: CpsValueId,
    },
    Primitive {
        dest: CpsValueId,
        op: core_ir::PrimitiveOp,
        args: Vec<CpsValueId>,
    },
    DirectCall {
        dest: CpsValueId,
        target: String,
        args: Vec<CpsValueId>,
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
    },
    UninstallHandler {
        handler: CpsHandlerId,
    },
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CpsRecordField {
    pub name: core_ir::Name,
    pub value: CpsValueId,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CpsHandlerEnv {
    pub entry: CpsContinuationId,
    pub values: Vec<CpsValueId>,
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
        effect: core_ir::Path,
        payload: CpsValueId,
        resume: CpsContinuationId,
        handler: CpsHandlerId,
        blocked: Option<CpsValueId>,
    },
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CpsHandler {
    pub id: CpsHandlerId,
    pub arms: Vec<CpsHandlerArm>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CpsHandlerArm {
    pub effect: core_ir::Path,
    pub entry: CpsContinuationId,
}

#[derive(Debug, Clone, PartialEq, Eq)]
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
