use yulang_core_ir as core_ir;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Module {
    pub path: core_ir::Path,
    pub bindings: Vec<Binding>,
    pub root_exprs: Vec<Expr>,
    pub roots: Vec<Root>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Binding {
    pub name: core_ir::Path,
    pub type_params: Vec<core_ir::TypeVar>,
    pub scheme: core_ir::Scheme,
    pub body: Expr,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Expr {
    pub ty: Type,
    pub kind: ExprKind,
}

impl Expr {
    pub fn typed(kind: ExprKind, ty: impl Into<Type>) -> Self {
        Self {
            ty: ty.into(),
            kind,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Type {
    Unknown,
    Core(core_ir::Type),
    Fun {
        param: Box<Type>,
        ret: Box<Type>,
    },
    Thunk {
        effect: core_ir::Type,
        value: Box<Type>,
    },
}

impl Type {
    pub fn unknown() -> Self {
        Self::Unknown
    }

    pub fn core(ty: core_ir::Type) -> Self {
        Self::Core(ty)
    }

    pub fn fun(param: Type, ret: Type) -> Self {
        Self::Fun {
            param: Box::new(param),
            ret: Box::new(ret),
        }
    }

    pub fn thunk(effect: core_ir::Type, value: Type) -> Self {
        Self::Thunk {
            effect,
            value: Box::new(value),
        }
    }

    pub fn as_core(&self) -> Option<&core_ir::Type> {
        match self {
            Type::Core(ty) => Some(ty),
            Type::Unknown | Type::Fun { .. } | Type::Thunk { .. } => None,
        }
    }
}

impl From<core_ir::Type> for Type {
    fn from(ty: core_ir::Type) -> Self {
        Type::Core(ty)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct EffectIdVar(pub usize);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum EffectIdRef {
    Var(EffectIdVar),
    Peek,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ExprKind {
    Var(core_ir::Path),
    EffectOp(core_ir::Path),
    PrimitiveOp(core_ir::PrimitiveOp),
    Lit(core_ir::Lit),
    Lambda {
        param: core_ir::Name,
        param_effect_annotation: Option<core_ir::ParamEffectAnnotation>,
        param_function_allowed_effects: Option<core_ir::FunctionSigAllowedEffects>,
        body: Box<Expr>,
    },
    Apply {
        callee: Box<Expr>,
        arg: Box<Expr>,
        evidence: Option<core_ir::ApplyEvidence>,
        instantiation: Option<TypeInstantiation>,
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
        tag: core_ir::Name,
        value: Option<Box<Expr>>,
    },
    Select {
        base: Box<Expr>,
        field: core_ir::Name,
    },
    Match {
        scrutinee: Box<Expr>,
        arms: Vec<MatchArm>,
        evidence: JoinEvidence,
    },
    Block {
        stmts: Vec<Stmt>,
        tail: Option<Box<Expr>>,
    },
    Handle {
        body: Box<Expr>,
        arms: Vec<HandleArm>,
        evidence: JoinEvidence,
        handler: HandleEffect,
    },
    BindHere {
        expr: Box<Expr>,
    },
    Thunk {
        effect: core_ir::Type,
        value: Type,
        expr: Box<Expr>,
    },
    LocalPushId {
        id: EffectIdVar,
        body: Box<Expr>,
    },
    PeekId,
    FindId {
        id: EffectIdRef,
    },
    AddId {
        id: EffectIdRef,
        allowed: core_ir::Type,
        thunk: Box<Expr>,
    },
    Coerce {
        from: core_ir::Type,
        to: core_ir::Type,
        expr: Box<Expr>,
    },
    Pack {
        var: core_ir::TypeVar,
        expr: Box<Expr>,
    },
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct JoinEvidence {
    pub result: core_ir::Type,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TypeInstantiation {
    pub target: core_ir::Path,
    pub args: Vec<TypeSubstitution>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TypeSubstitution {
    pub var: core_ir::TypeVar,
    pub ty: core_ir::Type,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Stmt {
    Let { pattern: Pattern, value: Expr },
    Expr(Expr),
    Module { def: core_ir::Path, body: Expr },
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Pattern {
    Wildcard {
        ty: Type,
    },
    Bind {
        name: core_ir::Name,
        ty: Type,
    },
    Lit {
        lit: core_ir::Lit,
        ty: Type,
    },
    Tuple {
        items: Vec<Pattern>,
        ty: Type,
    },
    List {
        prefix: Vec<Pattern>,
        spread: Option<Box<Pattern>>,
        suffix: Vec<Pattern>,
        ty: Type,
    },
    Record {
        fields: Vec<RecordPatternField>,
        spread: Option<RecordSpreadPattern>,
        ty: Type,
    },
    Variant {
        tag: core_ir::Name,
        value: Option<Box<Pattern>>,
        ty: Type,
    },
    Or {
        left: Box<Pattern>,
        right: Box<Pattern>,
        ty: Type,
    },
    As {
        pattern: Box<Pattern>,
        name: core_ir::Name,
        ty: Type,
    },
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RecordExprField {
    pub name: core_ir::Name,
    pub value: Expr,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum RecordSpreadExpr {
    Head(Box<Expr>),
    Tail(Box<Expr>),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RecordPatternField {
    pub name: core_ir::Name,
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
pub struct HandleArm {
    pub effect: core_ir::Path,
    pub payload: Pattern,
    pub resume: Option<ResumeBinding>,
    pub guard: Option<Expr>,
    pub body: Expr,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ResumeBinding {
    pub name: core_ir::Name,
    pub ty: Type,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct HandleEffect {
    pub consumes: Vec<core_ir::Path>,
    pub residual_before: Option<core_ir::Type>,
    pub residual_after: Option<core_ir::Type>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Root {
    Binding(core_ir::Path),
    Expr(usize),
}
