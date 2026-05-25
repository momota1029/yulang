//! Runtime IR data structures for Yulang.
//!
//! This crate owns the execution-facing expression tree and runtime type
//! witnesses. It does not lower, solve, monomorphize, validate, or execute the
//! tree; those responsibilities live in crates layered above this one.

use serde::{Deserialize, Serialize};
use yulang_typed_ir as typed_ir;

pub mod walk;

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct Module<T> {
    pub path: typed_ir::Path,
    pub bindings: Vec<Binding<T>>,
    pub root_exprs: Vec<Expr<T>>,
    pub roots: Vec<Root>,
    pub role_impls: Vec<typed_ir::RoleImplGraphNode>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct Binding<T> {
    pub name: typed_ir::Path,
    pub type_params: Vec<typed_ir::TypeVar>,
    pub scheme: typed_ir::Scheme,
    pub body: Expr<T>,
}

#[derive(Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Expr<T> {
    pub ty: T,
    pub kind: ExprKind<T>,
}

impl<T> Expr<T> {
    pub fn typed(kind: ExprKind<T>, ty: impl Into<T>) -> Self {
        Self {
            ty: ty.into(),
            kind,
        }
    }
}

impl<T: Clone> Clone for Expr<T> {
    fn clone(&self) -> Self {
        clone_expr_without_apply_spine_recursion(self)
    }
}

fn clone_expr_without_apply_spine_recursion<T: Clone>(expr: &Expr<T>) -> Expr<T> {
    enum Frame<'a, T> {
        Apply {
            ty: &'a T,
            arg: &'a Expr<T>,
            evidence: &'a Option<typed_ir::ApplyEvidence>,
            instantiation: &'a Option<TypeInstantiation>,
        },
        Select {
            ty: &'a T,
            field: &'a typed_ir::Name,
        },
        Variant {
            ty: &'a T,
            tag: &'a typed_ir::Name,
        },
        BindHere {
            ty: &'a T,
        },
        Thunk {
            ty: &'a T,
            effect: &'a typed_ir::Type,
            value: &'a T,
        },
        LocalPushId {
            ty: &'a T,
            id: EffectIdVar,
        },
        AddId {
            ty: &'a T,
            id: EffectIdRef,
            allowed: &'a typed_ir::Type,
            active: bool,
        },
        Coerce {
            ty: &'a T,
            from: &'a typed_ir::Type,
            to: &'a typed_ir::Type,
        },
        Pack {
            ty: &'a T,
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

#[derive(Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum RuntimeType {
    Unknown,
    Value(typed_ir::Type),
    Fun {
        param: Box<RuntimeType>,
        ret: Box<RuntimeType>,
    },
    Thunk {
        effect: typed_ir::Type,
        value: Box<RuntimeType>,
    },
}

impl RuntimeType {
    pub fn unknown() -> Self {
        Self::Unknown
    }

    pub fn value(ty: typed_ir::Type) -> Self {
        // NOTE: this can momentarily wrap a `typed_ir::Type::Fun` during the
        // lower stage (before monomorphize splits it into a Fun arm). The
        // monomorphize pass is responsible for normalizing those cases.
        Self::Value(ty)
    }

    pub fn fun(param: RuntimeType, ret: RuntimeType) -> Self {
        Self::Fun {
            param: Box::new(param),
            ret: Box::new(ret),
        }
    }

    pub fn thunk(effect: typed_ir::Type, value: RuntimeType) -> Self {
        Self::Thunk {
            effect,
            value: Box::new(value),
        }
    }

    pub fn as_value(&self) -> Option<&typed_ir::Type> {
        match self {
            RuntimeType::Value(ty) => Some(ty),
            RuntimeType::Unknown | RuntimeType::Fun { .. } | RuntimeType::Thunk { .. } => {
                None
            }
        }
    }
}

impl From<typed_ir::Type> for RuntimeType {
    fn from(ty: typed_ir::Type) -> Self {
        RuntimeType::Value(ty)
    }
}

impl Clone for RuntimeType {
    fn clone(&self) -> Self {
        clone_finalized_type_without_fun_spine_recursion(self)
    }
}

fn clone_finalized_type_without_fun_spine_recursion(ty: &RuntimeType) -> RuntimeType {
    enum Frame<'a> {
        Fun { param: &'a RuntimeType },
        Thunk { effect: &'a typed_ir::Type },
    }

    let mut current = ty;
    let mut frames = Vec::new();
    loop {
        match current {
            RuntimeType::Fun { param, ret } => {
                frames.push(Frame::Fun { param });
                current = ret;
            }
            RuntimeType::Thunk { effect, value } => {
                frames.push(Frame::Thunk { effect });
                current = value;
            }
            RuntimeType::Unknown => {
                let mut cloned = RuntimeType::Unknown;
                for frame in frames.into_iter().rev() {
                    cloned = match frame {
                        Frame::Fun { param } => RuntimeType::fun(param.clone(), cloned),
                        Frame::Thunk { effect } => RuntimeType::thunk(effect.clone(), cloned),
                    };
                }
                return cloned;
            }
            RuntimeType::Value(core) => {
                let mut cloned = RuntimeType::Value(core.clone());
                for frame in frames.into_iter().rev() {
                    cloned = match frame {
                        Frame::Fun { param } => RuntimeType::fun(param.clone(), cloned),
                        Frame::Thunk { effect } => RuntimeType::thunk(effect.clone(), cloned),
                    };
                }
                return cloned;
            }
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord, Serialize, Deserialize)]
pub struct EffectIdVar(pub usize);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord, Serialize, Deserialize)]
pub enum EffectIdRef {
    Var(EffectIdVar),
    Peek,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum ExprKind<T> {
    Var(typed_ir::Path),
    EffectOp(typed_ir::Path),
    PrimitiveOp(typed_ir::PrimitiveOp),
    Lit(typed_ir::Lit),
    Lambda {
        param: typed_ir::Name,
        param_effect_annotation: Option<typed_ir::ParamEffectAnnotation>,
        param_function_allowed_effects: Option<typed_ir::FunctionSigAllowedEffects>,
        body: Box<Expr<T>>,
    },
    Apply {
        callee: Box<Expr<T>>,
        arg: Box<Expr<T>>,
        evidence: Option<typed_ir::ApplyEvidence>,
        instantiation: Option<TypeInstantiation>,
    },
    If {
        cond: Box<Expr<T>>,
        then_branch: Box<Expr<T>>,
        else_branch: Box<Expr<T>>,
        evidence: Option<JoinEvidence>,
    },
    Tuple(Vec<Expr<T>>),
    Record {
        fields: Vec<RecordExprField<T>>,
        spread: Option<RecordSpreadExpr<T>>,
    },
    Variant {
        tag: typed_ir::Name,
        value: Option<Box<Expr<T>>>,
    },
    Select {
        base: Box<Expr<T>>,
        field: typed_ir::Name,
    },
    Match {
        scrutinee: Box<Expr<T>>,
        arms: Vec<MatchArm<T>>,
        evidence: JoinEvidence,
    },
    Block {
        stmts: Vec<Stmt<T>>,
        tail: Option<Box<Expr<T>>>,
    },
    Handle {
        body: Box<Expr<T>>,
        arms: Vec<HandleArm<T>>,
        evidence: JoinEvidence,
        handler: HandleEffect,
    },
    BindHere {
        expr: Box<Expr<T>>,
    },
    Thunk {
        effect: typed_ir::Type,
        value: T,
        expr: Box<Expr<T>>,
    },
    LocalPushId {
        id: EffectIdVar,
        body: Box<Expr<T>>,
    },
    PeekId,
    FindId {
        id: EffectIdRef,
    },
    AddId {
        id: EffectIdRef,
        allowed: typed_ir::Type,
        active: bool,
        thunk: Box<Expr<T>>,
    },
    Coerce {
        from: typed_ir::Type,
        to: typed_ir::Type,
        expr: Box<Expr<T>>,
    },
    Pack {
        var: typed_ir::TypeVar,
        expr: Box<Expr<T>>,
    },
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct JoinEvidence {
    pub result: typed_ir::Type,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct TypeInstantiation {
    pub target: typed_ir::Path,
    pub args: Vec<TypeSubstitution>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct TypeSubstitution {
    pub var: typed_ir::TypeVar,
    pub ty: typed_ir::Type,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum Stmt<T> {
    Let { pattern: Pattern<T>, value: Expr<T> },
    Expr(Expr<T>),
    Module { def: typed_ir::Path, body: Expr<T> },
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum Pattern<T> {
    Wildcard {
        ty: T,
    },
    Bind {
        name: typed_ir::Name,
        ty: T,
    },
    Lit {
        lit: typed_ir::Lit,
        ty: T,
    },
    Tuple {
        items: Vec<Pattern<T>>,
        ty: T,
    },
    List {
        prefix: Vec<Pattern<T>>,
        spread: Option<Box<Pattern<T>>>,
        suffix: Vec<Pattern<T>>,
        ty: T,
    },
    Record {
        fields: Vec<RecordPatternField<T>>,
        spread: Option<RecordSpreadPattern<T>>,
        ty: T,
    },
    Variant {
        tag: typed_ir::Name,
        value: Option<Box<Pattern<T>>>,
        ty: T,
    },
    Or {
        left: Box<Pattern<T>>,
        right: Box<Pattern<T>>,
        ty: T,
    },
    As {
        pattern: Box<Pattern<T>>,
        name: typed_ir::Name,
        ty: T,
    },
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct RecordExprField<T> {
    pub name: typed_ir::Name,
    pub value: Expr<T>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum RecordSpreadExpr<T> {
    Head(Box<Expr<T>>),
    Tail(Box<Expr<T>>),
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct RecordPatternField<T> {
    pub name: typed_ir::Name,
    pub pattern: Pattern<T>,
    pub default: Option<Expr<T>>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum RecordSpreadPattern<T> {
    Head(Box<Pattern<T>>),
    Tail(Box<Pattern<T>>),
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct MatchArm<T> {
    pub pattern: Pattern<T>,
    pub guard: Option<Expr<T>>,
    pub body: Expr<T>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct HandleArm<T> {
    pub effect: typed_ir::Path,
    pub payload: Pattern<T>,
    pub resume: Option<ResumeBinding<T>>,
    pub guard: Option<Expr<T>>,
    pub body: Expr<T>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct ResumeBinding<T> {
    pub name: typed_ir::Name,
    pub ty: T,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct HandleEffect {
    pub consumes: Vec<typed_ir::Path>,
    pub residual_before: Option<typed_ir::Type>,
    pub residual_after: Option<typed_ir::Type>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum Root {
    Binding(typed_ir::Path),
    Expr(usize),
}

pub type LoweredExpr = Expr<typed_ir::Type>;
pub type LoweredExprKind = ExprKind<typed_ir::Type>;
pub type LoweredModule = Module<typed_ir::Type>;
pub type LoweredBinding = Binding<typed_ir::Type>;
pub type LoweredStmt = Stmt<typed_ir::Type>;
pub type LoweredPattern = Pattern<typed_ir::Type>;
pub type LoweredRecordExprField = RecordExprField<typed_ir::Type>;
pub type LoweredRecordSpreadExpr = RecordSpreadExpr<typed_ir::Type>;
pub type LoweredRecordPatternField = RecordPatternField<typed_ir::Type>;
pub type LoweredRecordSpreadPattern = RecordSpreadPattern<typed_ir::Type>;
pub type LoweredMatchArm = MatchArm<typed_ir::Type>;
pub type LoweredHandleArm = HandleArm<typed_ir::Type>;
pub type LoweredResumeBinding = ResumeBinding<typed_ir::Type>;

pub type FinalizedExpr = Expr<RuntimeType>;
pub type FinalizedExprKind = ExprKind<RuntimeType>;
pub type FinalizedModule = Module<RuntimeType>;
pub type FinalizedBinding = Binding<RuntimeType>;
pub type FinalizedStmt = Stmt<RuntimeType>;
pub type FinalizedPattern = Pattern<RuntimeType>;
pub type FinalizedRecordExprField = RecordExprField<RuntimeType>;
pub type FinalizedRecordSpreadExpr = RecordSpreadExpr<RuntimeType>;
pub type FinalizedRecordPatternField = RecordPatternField<RuntimeType>;
pub type FinalizedRecordSpreadPattern = RecordSpreadPattern<RuntimeType>;
pub type FinalizedMatchArm = MatchArm<RuntimeType>;
pub type FinalizedHandleArm = HandleArm<RuntimeType>;
pub type FinalizedResumeBinding = ResumeBinding<RuntimeType>;

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn clones_deep_runtime_adapter_spine_without_recursing() {
        let mut expr =
            FinalizedExpr::typed(ExprKind::Lit(typed_ir::Lit::Unit), RuntimeType::unknown());
        for index in 0..20_000 {
            expr = match index % 3 {
                0 => FinalizedExpr::typed(
                    ExprKind::BindHere {
                        expr: Box::new(expr),
                    },
                    RuntimeType::unknown(),
                ),
                1 => FinalizedExpr::typed(
                    ExprKind::Thunk {
                        effect: typed_ir::Type::Unknown,
                        value: RuntimeType::unknown(),
                        expr: Box::new(expr),
                    },
                    RuntimeType::unknown(),
                ),
                _ => FinalizedExpr::typed(
                    ExprKind::Coerce {
                        from: typed_ir::Type::Unknown,
                        to: typed_ir::Type::Any,
                        expr: Box::new(expr),
                    },
                    RuntimeType::unknown(),
                ),
            };
        }

        let cloned = expr.clone();

        assert_eq!(cloned.ty, RuntimeType::unknown());
        std::mem::forget(expr);
        std::mem::forget(cloned);
    }
}
