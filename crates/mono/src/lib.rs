//! 単一化後の Yulang IR。
//!
//! `mono` は `poly` より後ろ、runtime lower より前の data crate である。
//! ここには推論途中の制約状態や typed evidence を入れない。

#![forbid(unsafe_code)]

pub mod dump;

use num_bigint::BigInt;

#[derive(Debug, Clone, PartialEq, Default)]
pub struct Program {
    pub roots: Vec<InstanceId>,
    pub instances: Vec<Instance>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct Instance {
    pub id: InstanceId,
    pub source: InstanceSource,
    pub signature: Signature,
    pub body: Expr,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct InstanceId(pub u32);

#[derive(Debug, Clone, PartialEq)]
pub enum InstanceSource {
    Def(DefId),
}

#[derive(Debug, Clone, PartialEq)]
pub struct Signature {
    pub text: String,
}

#[derive(Debug, Clone, PartialEq)]
pub struct Expr {
    pub kind: ExprKind,
}

impl Expr {
    pub fn new(kind: ExprKind) -> Self {
        Self { kind }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum ExprKind {
    Lit(Lit),
    PrimitiveOp(String),
    Local(DefId),
    InstanceRef(InstanceId),
    Apply(Box<Expr>, Box<Expr>),
    RefSet(Box<Expr>, Box<Expr>),
    Lambda(Pat, Box<Expr>),
    Tuple(Vec<Expr>),
    Record {
        fields: Vec<RecordField>,
        spread: RecordSpread<Box<Expr>>,
    },
    PolyVariant {
        tag: String,
        payloads: Vec<Expr>,
    },
    Select {
        base: Box<Expr>,
        name: String,
        resolution: Option<SelectResolution>,
    },
    Case {
        scrutinee: Box<Expr>,
        arms: Vec<CaseArm>,
    },
    Catch {
        body: Box<Expr>,
        arms: Vec<CatchArm>,
    },
    Block(Block),
}

#[derive(Debug, Clone, PartialEq)]
pub enum Lit {
    Int(i64),
    BigInt(BigInt),
    Float(f64),
    Str(String),
    Bool(bool),
    Unit,
}

#[derive(Debug, Clone, PartialEq)]
pub struct RecordField {
    pub name: String,
    pub value: Expr,
}

#[derive(Debug, Clone, PartialEq)]
pub struct CaseArm {
    pub pat: Pat,
    pub guard: Option<Expr>,
    pub body: Expr,
}

#[derive(Debug, Clone, PartialEq)]
pub struct CatchArm {
    pub pat: Pat,
    pub continuation: Option<Pat>,
    pub guard: Option<Expr>,
    pub body: Expr,
}

#[derive(Debug, Clone, PartialEq)]
pub struct Block {
    pub stmts: Vec<Stmt>,
    pub tail: Option<Box<Expr>>,
}

#[derive(Debug, Clone, PartialEq)]
pub enum Stmt {
    Let(Vis, Pat, Expr),
    Expr(Expr),
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
    Con(InstanceId, Vec<Pat>),
    Ref(InstanceId),
    Var(DefId),
    Or(Box<Pat>, Box<Pat>),
    As(Box<Pat>, DefId),
}

#[derive(Debug, Clone, PartialEq)]
pub enum RecordSpread<T> {
    Head(T),
    Tail(T),
    None,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SelectResolution {
    RecordField,
    Method { instance: InstanceId },
    TypeclassMethod { member: DefId },
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Vis {
    Pub,
    Our,
    My,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct DefId(pub u32);
