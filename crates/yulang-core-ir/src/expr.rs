use crate::graph::CoreGraphView;
use crate::names::{Name, Path};
use crate::types::{RecordField, RoleRequirement, Scheme, Type, TypeVar};

#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct PrincipalModule {
    pub path: Path,
    pub bindings: Vec<PrincipalBinding>,
    pub root_exprs: Vec<Expr>,
    pub roots: Vec<PrincipalRoot>,
}

#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct CoreProgram {
    pub program: PrincipalModule,
    pub graph: CoreGraphView,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ParamEffectAnnotation {
    Wildcard,
    Region(Name),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum FunctionSigAllowedEffects {
    Wildcard,
    Effects(Vec<Path>),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PrincipalBinding {
    pub name: Path,
    pub scheme: Scheme,
    pub body: Expr,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PrimitiveOp {
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
    IntAdd,
    IntSub,
    IntMul,
    IntDiv,
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
    StringConcat,
    IntToString,
    IntToHex,
    IntToUpperHex,
    FloatToString,
    BoolToString,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ApplyEvidence {
    pub arg_source_edge: Option<u32>,
    pub callee: crate::types::TypeBounds,
    pub arg: crate::types::TypeBounds,
    pub expected_arg: Option<crate::types::TypeBounds>,
    pub result: crate::types::TypeBounds,
    pub principal_callee: Option<crate::types::Type>,
    pub substitutions: Vec<crate::types::TypeSubstitution>,
    pub role_method: bool,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct JoinEvidence {
    pub result: crate::types::TypeBounds,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CoerceEvidence {
    pub source_edge: Option<u32>,
    pub actual: crate::types::TypeBounds,
    pub expected: crate::types::TypeBounds,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum PrincipalRoot {
    Binding(Path),
    Expr(usize),
}

#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct Module {
    pub path: Path,
    pub items: Vec<Item>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Binding {
    pub visibility: BindingVisibility,
    pub name: Name,
    pub scheme: Scheme,
    pub body: Expr,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RoleDecl {
    pub name: Path,
    pub params: Vec<TypeVar>,
    pub associated_types: Vec<Name>,
    pub members: Vec<RoleMember>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ImplDecl {
    pub role: Path,
    pub inputs: Vec<Type>,
    pub requirements: Vec<RoleRequirement>,
    pub associated_types: Vec<RecordField<Type>>,
    pub members: Vec<ImplMember>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Item {
    Binding(Binding),
    Role(RoleDecl),
    Impl(ImplDecl),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Expr {
    Var(Path),
    PrimitiveOp(PrimitiveOp),
    Lit(Lit),
    Lambda {
        param: Name,
        param_effect_annotation: Option<ParamEffectAnnotation>,
        param_function_allowed_effects: Option<FunctionSigAllowedEffects>,
        body: Box<Expr>,
    },
    Apply {
        callee: Box<Expr>,
        arg: Box<Expr>,
        evidence: Option<ApplyEvidence>,
    },
    If {
        cond: Box<Expr>,
        then_branch: Box<Expr>,
        else_branch: Box<Expr>,
        evidence: Option<JoinEvidence>,
    },
    Tuple(Vec<Expr>),
    Record {
        fields: Vec<RecordExprField>,
        spread: Option<RecordSpreadExpr>,
    },
    Variant {
        tag: Name,
        value: Option<Box<Expr>>,
    },
    Select {
        base: Box<Expr>,
        field: Name,
    },
    Match {
        scrutinee: Box<Expr>,
        arms: Vec<MatchArm>,
        evidence: Option<JoinEvidence>,
    },
    Block {
        stmts: Vec<Stmt>,
        tail: Option<Box<Expr>>,
    },
    Handle {
        body: Box<Expr>,
        arms: Vec<HandleArm>,
        evidence: Option<JoinEvidence>,
    },
    Coerce {
        expr: Box<Expr>,
        evidence: Option<CoerceEvidence>,
    },
    Pack {
        var: TypeVar,
        expr: Box<Expr>,
    },
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Pattern {
    Wildcard,
    Bind(Name),
    Lit(Lit),
    Tuple(Vec<Pattern>),
    List {
        prefix: Vec<Pattern>,
        spread: Option<Box<Pattern>>,
        suffix: Vec<Pattern>,
    },
    Record {
        fields: Vec<RecordPatternField>,
        spread: Option<RecordSpreadPattern>,
    },
    Variant {
        tag: Name,
        value: Option<Box<Pattern>>,
    },
    Or {
        left: Box<Pattern>,
        right: Box<Pattern>,
    },
    As {
        pattern: Box<Pattern>,
        name: Name,
    },
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RoleMember {
    pub name: Name,
    pub scheme: Scheme,
    pub has_receiver: bool,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ImplMember {
    pub name: Name,
    pub body: Binding,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RecordExprField {
    pub name: Name,
    pub value: Expr,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum RecordSpreadExpr {
    Head(Box<Expr>),
    Tail(Box<Expr>),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RecordPatternField {
    pub name: Name,
    pub pattern: Pattern,
    pub default: Option<Expr>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum RecordSpreadPattern {
    Head(Box<Pattern>),
    Tail(Box<Pattern>),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MatchArm {
    pub pattern: Pattern,
    pub guard: Option<Expr>,
    pub body: Expr,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Stmt {
    Let { pattern: Pattern, value: Expr },
    Expr(Expr),
    Module { def: Path, body: Box<Expr> },
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct HandleArm {
    pub effect: Path,
    pub payload: Pattern,
    pub resume: Option<Name>,
    pub guard: Option<Expr>,
    pub body: Expr,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BindingVisibility {
    Public,
    Private,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Lit {
    Int(String),
    Float(String),
    String(String),
    Bool(bool),
    Unit,
}
