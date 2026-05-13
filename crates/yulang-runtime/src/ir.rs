use yulang_typed_ir as typed_ir;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Module {
    pub path: typed_ir::Path,
    pub bindings: Vec<Binding>,
    pub root_exprs: Vec<Expr>,
    pub roots: Vec<Root>,
    pub role_impls: Vec<typed_ir::RoleImplGraphNode>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Binding {
    pub name: typed_ir::Path,
    pub type_params: Vec<typed_ir::TypeVar>,
    pub scheme: typed_ir::Scheme,
    pub body: Expr,
}

#[derive(Debug, PartialEq, Eq)]
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

impl Clone for Expr {
    fn clone(&self) -> Self {
        clone_expr_without_apply_spine_recursion(self)
    }
}

fn clone_expr_without_apply_spine_recursion(expr: &Expr) -> Expr {
    enum Frame<'a> {
        Apply {
            ty: &'a Type,
            arg: &'a Expr,
            evidence: &'a Option<typed_ir::ApplyEvidence>,
            instantiation: &'a Option<TypeInstantiation>,
        },
        Select {
            ty: &'a Type,
            field: &'a typed_ir::Name,
        },
        Variant {
            ty: &'a Type,
            tag: &'a typed_ir::Name,
        },
        BindHere {
            ty: &'a Type,
        },
        Thunk {
            ty: &'a Type,
            effect: &'a typed_ir::Type,
            value: &'a Type,
        },
        LocalPushId {
            ty: &'a Type,
            id: EffectIdVar,
        },
        AddId {
            ty: &'a Type,
            id: EffectIdRef,
            allowed: &'a typed_ir::Type,
            active: bool,
        },
        Coerce {
            ty: &'a Type,
            from: &'a typed_ir::Type,
            to: &'a typed_ir::Type,
        },
        Pack {
            ty: &'a Type,
            var: &'a typed_ir::TypeVar,
        },
    }

    let mut current = expr;
    let mut frames = Vec::new();
    loop {
        match &current.kind {
            ExprKind::Apply {
                callee,
                arg,
                evidence,
                instantiation,
            } => {
                frames.push(Frame::Apply {
                    ty: &current.ty,
                    arg,
                    evidence,
                    instantiation,
                });
                current = callee;
            }
            ExprKind::Select { base, field } => {
                frames.push(Frame::Select {
                    ty: &current.ty,
                    field,
                });
                current = base;
            }
            ExprKind::Variant {
                tag,
                value: Some(value),
            } => {
                frames.push(Frame::Variant {
                    ty: &current.ty,
                    tag,
                });
                current = value;
            }
            ExprKind::BindHere { expr } => {
                frames.push(Frame::BindHere { ty: &current.ty });
                current = expr;
            }
            ExprKind::Thunk {
                effect,
                value,
                expr,
            } => {
                frames.push(Frame::Thunk {
                    ty: &current.ty,
                    effect,
                    value,
                });
                current = expr;
            }
            ExprKind::LocalPushId { id, body } => {
                frames.push(Frame::LocalPushId {
                    ty: &current.ty,
                    id: *id,
                });
                current = body;
            }
            ExprKind::AddId {
                id,
                allowed,
                active,
                thunk,
            } => {
                frames.push(Frame::AddId {
                    ty: &current.ty,
                    id: *id,
                    allowed,
                    active: *active,
                });
                current = thunk;
            }
            ExprKind::Coerce { from, to, expr } => {
                frames.push(Frame::Coerce {
                    ty: &current.ty,
                    from,
                    to,
                });
                current = expr;
            }
            ExprKind::Pack { var, expr } => {
                frames.push(Frame::Pack {
                    ty: &current.ty,
                    var,
                });
                current = expr;
            }
            _ => break,
        }
    }

    let mut cloned = Expr {
        ty: current.ty.clone(),
        kind: current.kind.clone(),
    };
    for frame in frames.into_iter().rev() {
        cloned = match frame {
            Frame::Apply {
                ty,
                arg,
                evidence,
                instantiation,
            } => Expr {
                ty: ty.clone(),
                kind: ExprKind::Apply {
                    callee: Box::new(cloned),
                    arg: Box::new(arg.clone()),
                    evidence: evidence.clone(),
                    instantiation: instantiation.clone(),
                },
            },
            Frame::Select { ty, field } => Expr {
                ty: ty.clone(),
                kind: ExprKind::Select {
                    base: Box::new(cloned),
                    field: field.clone(),
                },
            },
            Frame::Variant { ty, tag } => Expr {
                ty: ty.clone(),
                kind: ExprKind::Variant {
                    tag: tag.clone(),
                    value: Some(Box::new(cloned)),
                },
            },
            Frame::BindHere { ty } => Expr {
                ty: ty.clone(),
                kind: ExprKind::BindHere {
                    expr: Box::new(cloned),
                },
            },
            Frame::Thunk { ty, effect, value } => Expr {
                ty: ty.clone(),
                kind: ExprKind::Thunk {
                    effect: effect.clone(),
                    value: value.clone(),
                    expr: Box::new(cloned),
                },
            },
            Frame::LocalPushId { ty, id } => Expr {
                ty: ty.clone(),
                kind: ExprKind::LocalPushId {
                    id,
                    body: Box::new(cloned),
                },
            },
            Frame::AddId {
                ty,
                id,
                allowed,
                active,
            } => Expr {
                ty: ty.clone(),
                kind: ExprKind::AddId {
                    id,
                    allowed: allowed.clone(),
                    active,
                    thunk: Box::new(cloned),
                },
            },
            Frame::Coerce { ty, from, to } => Expr {
                ty: ty.clone(),
                kind: ExprKind::Coerce {
                    from: from.clone(),
                    to: to.clone(),
                    expr: Box::new(cloned),
                },
            },
            Frame::Pack { ty, var } => Expr {
                ty: ty.clone(),
                kind: ExprKind::Pack {
                    var: var.clone(),
                    expr: Box::new(cloned),
                },
            },
        };
    }
    cloned
}

#[derive(Debug, PartialEq, Eq, Hash)]
pub enum Type {
    Unknown,
    Core(typed_ir::Type),
    Fun {
        param: Box<Type>,
        ret: Box<Type>,
    },
    Thunk {
        effect: typed_ir::Type,
        value: Box<Type>,
    },
}

impl Type {
    pub fn unknown() -> Self {
        Self::Unknown
    }

    pub fn core(ty: typed_ir::Type) -> Self {
        Self::Core(ty)
    }

    pub fn fun(param: Type, ret: Type) -> Self {
        Self::Fun {
            param: Box::new(param),
            ret: Box::new(ret),
        }
    }

    pub fn thunk(effect: typed_ir::Type, value: Type) -> Self {
        Self::Thunk {
            effect,
            value: Box::new(value),
        }
    }

    pub fn as_core(&self) -> Option<&typed_ir::Type> {
        match self {
            Type::Core(ty) => Some(ty),
            Type::Unknown | Type::Fun { .. } | Type::Thunk { .. } => None,
        }
    }
}

impl Clone for Type {
    fn clone(&self) -> Self {
        clone_type_without_fun_spine_recursion(self)
    }
}

fn clone_type_without_fun_spine_recursion(ty: &Type) -> Type {
    enum Frame<'a> {
        Fun { param: &'a Type },
        Thunk { effect: &'a typed_ir::Type },
    }

    let mut current = ty;
    let mut frames = Vec::new();
    loop {
        match current {
            Type::Fun { param, ret } => {
                frames.push(Frame::Fun { param });
                current = ret;
            }
            Type::Thunk { effect, value } => {
                frames.push(Frame::Thunk { effect });
                current = value;
            }
            Type::Unknown => {
                let mut cloned = Type::Unknown;
                for frame in frames.into_iter().rev() {
                    cloned = match frame {
                        Frame::Fun { param } => Type::fun(param.clone(), cloned),
                        Frame::Thunk { effect } => Type::thunk(effect.clone(), cloned),
                    };
                }
                return cloned;
            }
            Type::Core(core) => {
                let mut cloned = Type::Core(core.clone());
                for frame in frames.into_iter().rev() {
                    cloned = match frame {
                        Frame::Fun { param } => Type::fun(param.clone(), cloned),
                        Frame::Thunk { effect } => Type::thunk(effect.clone(), cloned),
                    };
                }
                return cloned;
            }
        }
    }
}

impl From<typed_ir::Type> for Type {
    fn from(ty: typed_ir::Type) -> Self {
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
    Var(typed_ir::Path),
    EffectOp(typed_ir::Path),
    PrimitiveOp(typed_ir::PrimitiveOp),
    Lit(typed_ir::Lit),
    Lambda {
        param: typed_ir::Name,
        param_effect_annotation: Option<typed_ir::ParamEffectAnnotation>,
        param_function_allowed_effects: Option<typed_ir::FunctionSigAllowedEffects>,
        body: Box<Expr>,
    },
    Apply {
        callee: Box<Expr>,
        arg: Box<Expr>,
        evidence: Option<typed_ir::ApplyEvidence>,
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
        tag: typed_ir::Name,
        value: Option<Box<Expr>>,
    },
    Select {
        base: Box<Expr>,
        field: typed_ir::Name,
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
        effect: typed_ir::Type,
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
        allowed: typed_ir::Type,
        active: bool,
        thunk: Box<Expr>,
    },
    Coerce {
        from: typed_ir::Type,
        to: typed_ir::Type,
        expr: Box<Expr>,
    },
    Pack {
        var: typed_ir::TypeVar,
        expr: Box<Expr>,
    },
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct JoinEvidence {
    pub result: typed_ir::Type,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TypeInstantiation {
    pub target: typed_ir::Path,
    pub args: Vec<TypeSubstitution>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TypeSubstitution {
    pub var: typed_ir::TypeVar,
    pub ty: typed_ir::Type,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Stmt {
    Let { pattern: Pattern, value: Expr },
    Expr(Expr),
    Module { def: typed_ir::Path, body: Expr },
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Pattern {
    Wildcard {
        ty: Type,
    },
    Bind {
        name: typed_ir::Name,
        ty: Type,
    },
    Lit {
        lit: typed_ir::Lit,
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
        tag: typed_ir::Name,
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
        name: typed_ir::Name,
        ty: Type,
    },
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RecordExprField {
    pub name: typed_ir::Name,
    pub value: Expr,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum RecordSpreadExpr {
    Head(Box<Expr>),
    Tail(Box<Expr>),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RecordPatternField {
    pub name: typed_ir::Name,
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
    pub effect: typed_ir::Path,
    pub payload: Pattern,
    pub resume: Option<ResumeBinding>,
    pub guard: Option<Expr>,
    pub body: Expr,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ResumeBinding {
    pub name: typed_ir::Name,
    pub ty: Type,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct HandleEffect {
    pub consumes: Vec<typed_ir::Path>,
    pub residual_before: Option<typed_ir::Type>,
    pub residual_after: Option<typed_ir::Type>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Root {
    Binding(typed_ir::Path),
    Expr(usize),
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn clones_deep_runtime_adapter_spine_without_recursing() {
        let mut expr = Expr::typed(ExprKind::Lit(typed_ir::Lit::Unit), Type::unknown());
        for index in 0..20_000 {
            expr = match index % 3 {
                0 => Expr::typed(
                    ExprKind::BindHere {
                        expr: Box::new(expr),
                    },
                    Type::unknown(),
                ),
                1 => Expr::typed(
                    ExprKind::Thunk {
                        effect: typed_ir::Type::Unknown,
                        value: Type::unknown(),
                        expr: Box::new(expr),
                    },
                    Type::unknown(),
                ),
                _ => Expr::typed(
                    ExprKind::Coerce {
                        from: typed_ir::Type::Unknown,
                        to: typed_ir::Type::Any,
                        expr: Box::new(expr),
                    },
                    Type::unknown(),
                ),
            };
        }

        let cloned = expr.clone();

        assert_eq!(cloned.ty, Type::unknown());
        std::mem::forget(expr);
        std::mem::forget(cloned);
    }
}
