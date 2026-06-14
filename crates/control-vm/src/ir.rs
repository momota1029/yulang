//! Lightweight control IR lowered from `mono`.

use mono::{
    ComputationType, EffectiveThunkType, FunctionAdapterHygiene, Lit, PrimitiveContext,
    PrimitiveOp, Type,
};

#[derive(Debug, Clone, PartialEq, Default)]
pub struct Program {
    pub roots: Vec<Root>,
    pub instances: Vec<Instance>,
    pub exprs: Vec<Expr>,
}

#[derive(Debug, Clone, PartialEq)]
pub enum Root {
    Instance(InstanceId),
    Expr(ExprId),
}

#[derive(Debug, Clone, PartialEq)]
pub struct Instance {
    pub id: InstanceId,
    pub source: mono::InstanceSource,
    pub signature: mono::Signature,
    pub entry: ExprId,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct ExprId(pub u32);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct DefId(pub u32);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct InstanceId(pub u32);

#[derive(Debug, Clone, PartialEq)]
pub enum Expr {
    Lit(Lit),
    PrimitiveOp {
        op: PrimitiveOp,
        context: PrimitiveContext,
    },
    Constructor {
        def: DefId,
        arity: usize,
    },
    EffectOp {
        path: Vec<String>,
    },
    Local(DefId),
    InstanceRef(InstanceId),
    Coerce {
        source: Type,
        target: Type,
        expr: ExprId,
    },
    MakeThunk {
        source: ComputationType,
        target: EffectiveThunkType,
        body: ExprId,
    },
    ForceThunk {
        source: EffectiveThunkType,
        target: ComputationType,
        thunk: ExprId,
    },
    FunctionAdapter {
        source: Type,
        target: Type,
        function: ExprId,
        hygiene: FunctionAdapterHygiene,
    },
    MarkerFrame {
        path: Vec<String>,
        body: ExprId,
    },
    Apply {
        callee: ExprId,
        arg: ExprId,
    },
    RefSet {
        reference: ExprId,
        value: ExprId,
    },
    Lambda {
        param: Pat,
        body: ExprId,
    },
    Tuple(Vec<ExprId>),
    Record {
        fields: Vec<RecordField>,
        spread: RecordSpread<ExprId>,
    },
    PolyVariant {
        tag: String,
        payloads: Vec<ExprId>,
    },
    Select {
        base: ExprId,
        name: String,
        resolution: Option<SelectResolution>,
    },
    Case {
        scrutinee: ExprId,
        arms: Vec<CaseArm>,
    },
    Catch {
        body: ExprId,
        arms: Vec<CatchArm>,
    },
    Block(Block),
}

#[derive(Debug, Clone, PartialEq)]
pub struct RecordField {
    pub name: String,
    pub value: ExprId,
}

#[derive(Debug, Clone, PartialEq)]
pub enum RecordSpread<T> {
    None,
    Head(T),
    Tail(T),
}

#[derive(Debug, Clone, PartialEq)]
pub enum SelectResolution {
    RecordField,
    Method { instance: InstanceId },
    TypeclassMethod { member: DefId },
}

#[derive(Debug, Clone, PartialEq)]
pub struct CaseArm {
    pub pat: Pat,
    pub guard: Option<ExprId>,
    pub body: ExprId,
}

#[derive(Debug, Clone, PartialEq)]
pub struct CatchArm {
    pub operation_path: Option<Vec<String>>,
    pub pat: Pat,
    pub continuation: Option<Pat>,
    pub guard: Option<ExprId>,
    pub body: ExprId,
}

#[derive(Debug, Clone, PartialEq)]
pub struct Block {
    pub stmts: Vec<Stmt>,
    pub tail: Option<ExprId>,
}

#[derive(Debug, Clone, PartialEq)]
pub enum Stmt {
    Let(mono::Vis, Pat, ExprId),
    Expr(ExprId),
    Module(DefId, Vec<Stmt>),
}

#[derive(Debug, Clone, PartialEq)]
pub enum Pat {
    Wild,
    Lit(Lit),
    Tuple(Vec<Pat>),
    List {
        prefix: Vec<Pat>,
        spread: Option<Box<Pat>>,
        suffix: Vec<Pat>,
    },
    Record {
        fields: Vec<(String, Pat)>,
        spread: RecordSpread<DefId>,
    },
    PolyVariant(String, Vec<Pat>),
    Con(DefId, Vec<Pat>),
    Ref(InstanceId),
    Var(DefId),
    Or(Box<Pat>, Box<Pat>),
    As(Box<Pat>, DefId),
}
