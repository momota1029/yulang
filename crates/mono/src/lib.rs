//! 単一化後の Yulang IR。
//!
//! `mono` は `poly` より後ろ、runtime lower より前の data crate である。
//! ここには推論途中の制約状態や typed evidence を入れない。

#![forbid(unsafe_code)]

pub mod dump;

use num_bigint::BigInt;
use serde::{Deserialize, Serialize};

#[derive(Debug, Clone, PartialEq, Default, Serialize, Deserialize)]
pub struct Program {
    pub roots: Vec<Root>,
    pub instances: Vec<Instance>,
}

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub enum Root {
    Instance(InstanceId),
    EvalInstance(InstanceId),
    Expr(Expr),
}

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct Instance {
    pub id: InstanceId,
    pub source: InstanceSource,
    pub signature: Signature,
    pub body: Expr,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord, Serialize, Deserialize)]
pub struct InstanceId(pub u32);

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub enum InstanceSource {
    Def(DefId),
}

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct Signature {
    pub ty: Type,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum Type {
    Any,
    Never,
    Con {
        path: Vec<String>,
        args: Vec<Type>,
    },
    Fun {
        arg: Box<Type>,
        arg_effect: Box<Type>,
        ret_effect: Box<Type>,
        ret: Box<Type>,
    },
    Thunk {
        effect: Box<Type>,
        value: Box<Type>,
    },
    Record(Vec<TypeField>),
    PolyVariant(Vec<TypeVariant>),
    Tuple(Vec<Type>),
    EffectRow(Vec<Type>),
    Stack {
        inner: Box<Type>,
        weight: StackWeight,
    },
    Union(Box<Type>, Box<Type>),
    Intersection(Box<Type>, Box<Type>),
    OpenVar(u32),
}

impl Type {
    pub fn unit() -> Self {
        Self::Con {
            path: vec!["unit".to_string()],
            args: Vec::new(),
        }
    }

    pub fn pure_effect() -> Self {
        Self::EffectRow(Vec::new())
    }

    pub fn is_pure_effect(&self) -> bool {
        matches!(self, Self::Never) || matches!(self, Self::EffectRow(items) if items.is_empty())
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct TypeField {
    pub name: String,
    pub value: Type,
    pub optional: bool,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct TypeVariant {
    pub name: String,
    pub payloads: Vec<Type>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct StackWeight {
    pub entries: Vec<StackWeightEntry>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct StackWeightEntry {
    pub id: u32,
    pub pops: u32,
    pub floor: Vec<EffectFamilies>,
    pub stack: Vec<EffectFamilies>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum EffectFamilies {
    Empty,
    All,
    AllExcept(Vec<EffectFamily>),
    Set(Vec<EffectFamily>),
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct EffectFamily {
    pub path: Vec<String>,
    pub args: Vec<Type>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct ComputationType {
    pub effect: Type,
    pub value: Type,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct EffectiveThunkType {
    pub effect: Type,
    pub value: Type,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, Default, Serialize, Deserialize)]
pub struct FunctionAdapterHygiene {
    pub markers: Vec<GuardMarker>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct GuardMarker {
    pub path: Vec<String>,
    pub depth: u32,
    #[serde(default)]
    pub guard_own_path: bool,
    #[serde(default = "guard_marker_default_foreign_path")]
    pub guard_foreign_path: bool,
}

fn guard_marker_default_foreign_path() -> bool {
    true
}

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct Expr {
    pub kind: ExprKind,
}

impl Expr {
    pub fn new(kind: ExprKind) -> Self {
        Self { kind }
    }
}

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub enum ExprKind {
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
        expr: Box<Expr>,
    },
    MakeThunk {
        source: ComputationType,
        target: EffectiveThunkType,
        body: Box<Expr>,
    },
    ForceThunk {
        source: EffectiveThunkType,
        target: ComputationType,
        thunk: Box<Expr>,
    },
    FunctionAdapter {
        source: Type,
        target: Type,
        function: Box<Expr>,
        hygiene: FunctionAdapterHygiene,
    },
    MarkerFrame {
        path: Vec<String>,
        body: Box<Expr>,
    },
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

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum PrimitiveOp {
    YadaYada,
    BoolNot,
    BoolEq,
    ListEmpty,
    ListSingleton,
    ListLen,
    ListMerge,
    ListIndex,
    ListIndexRange,
    ListSplice,
    ListIndexRangeRaw,
    ListSpliceRaw,
    ListViewRaw,
    StringLen,
    StringIndex,
    StringIndexRange,
    StringSplice,
    StringIndexRangeRaw,
    StringSpliceRaw,
    StringLineCount,
    StringLineRange,
    IntAdd,
    IntSub,
    IntMul,
    IntDiv,
    IntMod,
    IntEq,
    IntLt,
    IntLe,
    IntGt,
    IntGe,
    FloatAdd,
    FloatSub,
    FloatMul,
    FloatDiv,
    FloatEq,
    FloatLt,
    FloatLe,
    FloatGt,
    FloatGe,
    StringEq,
    StringConcat,
    StringToBytes,
    CharEq,
    CharToString,
    CharIsWhitespace,
    CharIsPunctuation,
    CharIsWord,
    BytesLen,
    BytesEq,
    BytesConcat,
    BytesIndex,
    BytesIndexRange,
    BytesToUtf8Raw,
    BytesToPath,
    PathToBytes,
    IntToString,
    IntToHex,
    IntToUpperHex,
    IntToFloat,
    FloatToString,
    BoolToString,
}

impl PrimitiveOp {
    pub fn arity(self) -> usize {
        match self {
            Self::YadaYada => 0,
            Self::BoolNot
            | Self::ListEmpty
            | Self::ListSingleton
            | Self::ListLen
            | Self::ListViewRaw
            | Self::StringLen
            | Self::StringLineCount
            | Self::StringToBytes
            | Self::BytesLen
            | Self::BytesToUtf8Raw
            | Self::BytesToPath
            | Self::PathToBytes
            | Self::IntToString
            | Self::IntToHex
            | Self::IntToUpperHex
            | Self::IntToFloat
            | Self::FloatToString
            | Self::BoolToString
            | Self::CharToString
            | Self::CharIsWhitespace
            | Self::CharIsPunctuation
            | Self::CharIsWord => 1,
            Self::ListMerge
            | Self::ListIndex
            | Self::ListIndexRange
            | Self::StringIndex
            | Self::StringIndexRange
            | Self::StringLineRange
            | Self::BoolEq
            | Self::IntAdd
            | Self::IntSub
            | Self::IntMul
            | Self::IntDiv
            | Self::IntMod
            | Self::IntEq
            | Self::IntLt
            | Self::IntLe
            | Self::IntGt
            | Self::IntGe
            | Self::FloatAdd
            | Self::FloatSub
            | Self::FloatMul
            | Self::FloatDiv
            | Self::FloatEq
            | Self::FloatLt
            | Self::FloatLe
            | Self::FloatGt
            | Self::FloatGe
            | Self::StringEq
            | Self::StringConcat
            | Self::CharEq
            | Self::BytesEq
            | Self::BytesConcat
            | Self::BytesIndex
            | Self::BytesIndexRange => 2,
            Self::ListSplice
            | Self::ListIndexRangeRaw
            | Self::StringSplice
            | Self::StringIndexRangeRaw => 3,
            Self::ListSpliceRaw | Self::StringSpliceRaw => 4,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, Default, Serialize, Deserialize)]
pub struct PrimitiveContext {
    pub list_view: Option<ListViewConstructors>,
    pub range: Option<RangeConstructors>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct ListViewConstructors {
    pub empty: DefId,
    pub leaf: DefId,
    pub node: DefId,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct RangeConstructors {
    pub within: DefId,
    pub unbounded: DefId,
    pub included: DefId,
    pub excluded: DefId,
}

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub enum Lit {
    Int(i64),
    BigInt(BigInt),
    Float(f64),
    Str(String),
    Bool(bool),
    Unit,
}

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct RecordField {
    pub name: String,
    pub value: Expr,
}

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct RecordPatField {
    pub name: String,
    pub pat: Pat,
    pub default: Option<Expr>,
}

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct CaseArm {
    pub pat: Pat,
    pub guard: Option<Expr>,
    pub body: Expr,
}

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct CatchArm {
    pub operation_path: Option<Vec<String>>,
    pub pat: Pat,
    pub continuation: Option<Pat>,
    pub guard: Option<Expr>,
    pub body: Expr,
}

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct Block {
    pub stmts: Vec<Stmt>,
    pub tail: Option<Box<Expr>>,
}

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub enum Stmt {
    Let(Vis, Pat, Expr),
    Expr(Expr),
    Module(DefId, Vec<Stmt>),
}

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
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
        fields: Vec<RecordPatField>,
        spread: RecordSpread<DefId>,
    },
    PolyVariant(String, Vec<Pat>),
    Con(DefId, Vec<Pat>),
    Ref(InstanceId),
    Var(DefId),
    Or(Box<Pat>, Box<Pat>),
    As(Box<Pat>, DefId),
}

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub enum RecordSpread<T> {
    Head(T),
    Tail(T),
    None,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum SelectResolution {
    RecordField,
    Method { instance: InstanceId },
    TypeclassMethod { member: DefId },
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum Vis {
    Pub,
    Our,
    My,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord, Serialize, Deserialize)]
pub struct DefId(pub u32);
