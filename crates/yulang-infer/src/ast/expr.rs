use crate::ids::{DefId, RefId, TypeVar};
use crate::symbols::{Name, Path};
use yulang_typed_ir as typed_ir;

/// 計算としての式型。
///
/// `value` は式が返す値、`effect` は評価中に発生しうる effect row。
/// 理論上は `thunk[effect, value]` に対応する。
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct ComputationTy {
    pub value: TypeVar,
    pub effect: TypeVar,
}

impl ComputationTy {
    pub fn new(value: TypeVar, effect: TypeVar) -> Self {
        Self { value, effect }
    }
}

/// 型変数つき式。
///
/// 既存コードとの互換のため `tv` / `eff` フィールドを残しているが、意味上は
/// `ComputationTy { value: tv, effect: eff }` が主役。
#[derive(Debug, Clone)]
pub struct TypedExpr {
    pub tv: TypeVar,
    pub eff: TypeVar,
    pub kind: ExprKind,
}

impl TypedExpr {
    pub fn new(ty: ComputationTy, kind: ExprKind) -> Self {
        Self {
            tv: ty.value,
            eff: ty.effect,
            kind,
        }
    }

    pub fn computation_ty(&self) -> ComputationTy {
        ComputationTy::new(self.tv, self.eff)
    }
}

#[derive(Debug, Clone)]
pub enum Lit {
    Int(String),
    Float(f64),
    Str(String),
    Bool(bool),
    Unit,
}

#[derive(Debug, Clone)]
pub enum ExprKind {
    Lit(Lit),
    PrimitiveOp(typed_ir::PrimitiveOp),
    Var(DefId),
    Ref(RefId),
    App {
        callee: Box<TypedExpr>,
        arg: Box<TypedExpr>,
        callee_edge_id: Option<crate::diagnostic::ExpectedEdgeId>,
        expected_callee_tv: TypeVar,
        arg_edge_id: Option<crate::diagnostic::ExpectedEdgeId>,
        expected_arg_tv: TypeVar,
    },
    RefSet {
        reference: Box<TypedExpr>,
        value: Box<TypedExpr>,
    },
    Lam(DefId, Box<TypedExpr>),
    Tuple(Vec<TypedExpr>),
    Record {
        fields: Vec<(Name, TypedExpr)>,
        spread: Option<RecordSpread>,
    },
    PolyVariant(Name, Vec<TypedExpr>, PolyVariantOrigin),
    Select {
        recv: Box<TypedExpr>,
        name: Name,
    },
    Match(Box<TypedExpr>, Vec<TypedMatchArm>),
    Catch(Box<TypedExpr>, Vec<TypedCatchArm>),
    Block(TypedBlock),
    BindHere(Box<TypedExpr>),
    Coerce {
        edge_id: Option<crate::diagnostic::ExpectedEdgeId>,
        actual_tv: TypeVar,
        expected_tv: TypeVar,
        expr: Box<TypedExpr>,
    },
    PackForall(TypeVar, Box<TypedExpr>),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PolyVariantOrigin {
    Syntax,
    Constructor,
}

#[derive(Debug, Clone)]
pub enum RecordSpread {
    Head(Box<TypedExpr>),
    Tail(Box<TypedExpr>),
}

#[derive(Debug, Clone)]
pub struct TypedBlock {
    pub tv: TypeVar,
    pub eff: TypeVar,
    pub stmts: Vec<TypedStmt>,
    pub tail: Option<Box<TypedExpr>>,
}

impl TypedBlock {
    pub fn computation_ty(&self) -> ComputationTy {
        ComputationTy::new(self.tv, self.eff)
    }
}

#[derive(Debug, Clone)]
pub enum TypedStmt {
    Let(TypedPat, TypedExpr),
    Expr(TypedExpr),
    Module(DefId, TypedBlock),
}

#[derive(Debug, Clone)]
pub struct TypedMatchArm {
    pub pat: TypedPat,
    pub guard: Option<TypedExpr>,
    pub body: TypedExpr,
}

#[derive(Debug, Clone)]
pub struct TypedCatchArm {
    pub tv: TypeVar,
    pub guard: Option<TypedExpr>,
    pub kind: CatchArmKind,
}

#[derive(Debug, Clone)]
pub enum CatchArmKind {
    Value(TypedPat, TypedExpr),
    Effect {
        op_path: Path,
        pat: TypedPat,
        k: DefId,
        body: TypedExpr,
    },
}

#[derive(Debug, Clone)]
pub struct TypedPat {
    pub tv: TypeVar,
    pub kind: PatKind,
}

#[derive(Debug, Clone)]
pub struct RecordPatField {
    pub name: Name,
    pub pat: TypedPat,
    pub default: Option<TypedExpr>,
}

#[derive(Debug, Clone)]
pub enum RecordPatSpread {
    Head(Box<TypedPat>),
    Tail(Box<TypedPat>),
}

#[derive(Debug, Clone)]
pub enum PatKind {
    Wild,
    Lit(Lit),
    Tuple(Vec<TypedPat>),
    List {
        prefix: Vec<TypedPat>,
        spread: Option<Box<TypedPat>>,
        suffix: Vec<TypedPat>,
    },
    Record {
        spread: Option<RecordPatSpread>,
        fields: Vec<RecordPatField>,
    },
    PolyVariant(Name, Vec<TypedPat>),
    Con(RefId, Option<Box<TypedPat>>),
    UnresolvedName(Name),
    Or(Box<TypedPat>, Box<TypedPat>),
    As(Box<TypedPat>, DefId),
}
