//! Typed monomorphic IR produced by elaboration.
//!
//! This crate is a data boundary. `yulang-elaborate` builds this IR from
//! `InferExport`; runtime lowering consumes it. The tree can carry concrete
//! type and effect information because it is produced after monomorphization,
//! not by reusing infer's typed expression evidence.

use std::collections::{BTreeMap, BTreeSet};
use std::fmt;

use serde::de;
use serde::{Deserialize, Serialize};
use yulang_erased_ir::{
    DefId, Lit, Name, Path, PrimitiveOp, RecordSpread, RefId, ResolvedTypeClassRef, Type, TypeArg,
    TypeVar, VariantCase,
};

#[derive(Debug, Clone, PartialEq, Eq, Default, Serialize, Deserialize)]
pub struct ElaboratedProgram {
    pub module: ElaboratedModule,
    pub refs: ResolvedRefTable,
}

#[derive(Debug, Clone, PartialEq, Eq, Default, Serialize, Deserialize)]
pub struct ElaboratedModule {
    pub path: Path,
    pub instances: Vec<MonoInstance>,
    pub root_exprs: Vec<ElaboratedExpr>,
    pub roots: Vec<ElaboratedRoot>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct MonoInstance {
    pub id: MonoInstanceId,
    pub source: DemandSource,
    pub signature: MonoComputation,
    pub body: ElaboratedExpr,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord, Serialize, Deserialize)]
pub struct MonoInstanceId(pub u32);

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum DemandSource {
    Def(DefId),
    RootExpr(usize),
    TypeclassRef { ref_id: RefId },
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum ElaboratedRoot {
    Instance(MonoInstanceId),
    Expr(usize),
}

#[derive(Debug, Clone, PartialEq, Eq, Default, Serialize, Deserialize)]
pub struct ResolvedRefTable {
    pub entries: BTreeMap<ResolvedRefKey, ResolvedRef>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord, Serialize, Deserialize)]
pub struct ResolvedRefKey {
    pub instance: MonoInstanceId,
    pub ref_id: RefId,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct ResolvedRef {
    pub target: MonoInstanceId,
    pub source: ResolvedRefSource,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum ResolvedRefSource {
    Direct { def: DefId },
    InferResolvedTypeclass { resolved: ResolvedTypeClassRef },
    ElaboratedTypeclass { resolved: ResolvedTypeClassRef },
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct MonoComputation {
    pub value: MonoType,
    pub effect: MonoEffect,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum MonoType {
    Value(ConcreteType),
    EffectiveThunk(EffectiveThunkType),
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct EffectiveThunkType {
    pub effect: MonoEffect,
    pub value: Box<MonoType>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct MonoEffect {
    row: ConcreteType,
}

impl MonoEffect {
    pub fn new(row: ConcreteType) -> Self {
        Self { row }
    }

    pub fn row(&self) -> &ConcreteType {
        &self.row
    }

    pub fn into_row(self) -> ConcreteType {
        self.row
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize)]
#[serde(transparent)]
pub struct ConcreteType {
    ty: Type,
}

impl ConcreteType {
    pub fn try_from_type(ty: Type) -> Result<Self, ConcreteTypeError> {
        validate_concrete_type(&ty, &mut BTreeSet::new())?;
        Ok(Self { ty })
    }

    pub fn as_type(&self) -> &Type {
        &self.ty
    }

    pub fn into_type(self) -> Type {
        self.ty
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ConcreteTypeError {
    Unknown,
    FreeVar(TypeVar),
}

impl fmt::Display for ConcreteTypeError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Unknown => write!(f, "unknown type is not concrete"),
            Self::FreeVar(var) => write!(f, "free type variable is not concrete: {}", var.0),
        }
    }
}

impl std::error::Error for ConcreteTypeError {}

impl<'de> Deserialize<'de> for ConcreteType {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        let ty = Type::deserialize(deserializer)?;
        Self::try_from_type(ty).map_err(de::Error::custom)
    }
}

#[derive(Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ElaboratedExpr {
    pub comp: MonoComputation,
    pub kind: ElaboratedExprKind,
}

impl ElaboratedExpr {
    pub fn new(kind: ElaboratedExprKind, comp: MonoComputation) -> Self {
        Self { comp, kind }
    }
}

impl Clone for ElaboratedExpr {
    fn clone(&self) -> Self {
        clone_expr_without_boundary_spine_recursion(self)
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum ElaboratedExprKind {
    Def(DefId),
    Ref(RefId),
    PrimitiveOp(PrimitiveOp),
    Lit(Lit),
    Lambda {
        param: DefId,
        param_type: MonoType,
        body: Box<ElaboratedExpr>,
    },
    Apply {
        callee: Box<ElaboratedExpr>,
        arg: Box<ElaboratedExpr>,
    },
    RefSet {
        reference: Box<ElaboratedExpr>,
        value: Box<ElaboratedExpr>,
    },
    Tuple(Vec<ElaboratedExpr>),
    Record {
        fields: Vec<RecordExprField>,
        spread: Option<RecordSpreadExpr>,
    },
    Variant {
        tag: Name,
        value: Option<Box<ElaboratedExpr>>,
    },
    Select {
        base: Box<ElaboratedExpr>,
        field: Name,
    },
    Match {
        scrutinee: Box<ElaboratedExpr>,
        arms: Vec<MatchArm>,
    },
    Handle {
        body: Box<ElaboratedExpr>,
        arms: Vec<HandleArm>,
    },
    Block(ElaboratedBlock),
    MakeThunk {
        body: Box<ElaboratedExpr>,
        thunk: EffectiveThunkType,
    },
    LocalPushId {
        id: EffectIdVar,
        body: Box<ElaboratedExpr>,
    },
    PeekId,
    FindId {
        id: EffectIdRef,
    },
    AddId {
        id: EffectIdRef,
        allowed: MonoEffect,
        active: bool,
        thunk: Box<ElaboratedExpr>,
    },
    ForceThunk {
        thunk: Box<ElaboratedExpr>,
        source: EffectiveThunkType,
        target: MonoComputation,
    },
    Cast {
        expr: Box<ElaboratedExpr>,
        source: MonoType,
        target: MonoType,
    },
    FunctionAdapter {
        function: Box<ElaboratedExpr>,
        adapter: FunctionAdapter,
    },
    Pack {
        var: TypeVar,
        expr: Box<ElaboratedExpr>,
    },
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct FunctionAdapter {
    pub source: FunctionBoundary,
    pub target: FunctionBoundary,
    pub call: FunctionAdapterCall,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct FunctionBoundary {
    pub param: MonoType,
    pub param_effect: MonoEffect,
    pub ret_effect: MonoEffect,
    pub ret: MonoType,
}

#[derive(Debug, Clone, PartialEq, Eq, Default, Serialize, Deserialize)]
pub struct FunctionAdapterCall {
    pub local_scope: Option<EffectIdVar>,
    pub result_boundaries: Vec<FunctionResultBoundary>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum FunctionResultBoundary {
    AddId {
        id: EffectIdRef,
        allowed: MonoEffect,
        active: bool,
    },
    FunctionAdapter(Box<FunctionAdapter>),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord, Serialize, Deserialize)]
pub struct EffectIdVar(pub u32);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord, Serialize, Deserialize)]
pub enum EffectIdRef {
    Var(EffectIdVar),
    Peek,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct ElaboratedBlock {
    pub stmts: Vec<ElaboratedStmt>,
    pub tail: Option<Box<ElaboratedExpr>>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum ElaboratedStmt {
    Let {
        pattern: Pattern,
        value: ElaboratedExpr,
    },
    Expr(ElaboratedExpr),
    Module {
        def: DefId,
        body: ElaboratedBlock,
    },
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct MatchArm {
    pub pattern: Pattern,
    pub guard: Option<ElaboratedExpr>,
    pub body: ElaboratedExpr,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct HandleArm {
    pub effect: Path,
    pub payload: Pattern,
    pub resume: Option<ResumeBinding>,
    pub guard: Option<ElaboratedExpr>,
    pub body: ElaboratedExpr,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct ResumeBinding {
    pub def: DefId,
    pub typ: MonoType,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum Pattern {
    Wildcard {
        typ: MonoType,
    },
    Bind {
        def: DefId,
        typ: MonoType,
    },
    Lit {
        lit: Lit,
        typ: MonoType,
    },
    Tuple {
        items: Vec<Pattern>,
        typ: MonoType,
    },
    List {
        prefix: Vec<Pattern>,
        spread: Option<Box<Pattern>>,
        suffix: Vec<Pattern>,
        typ: MonoType,
    },
    Record {
        fields: Vec<RecordPatternField>,
        spread: Option<RecordSpreadPattern>,
        typ: MonoType,
    },
    Variant {
        tag: Name,
        value: Option<Box<Pattern>>,
        typ: MonoType,
    },
    Or {
        left: Box<Pattern>,
        right: Box<Pattern>,
        typ: MonoType,
    },
    As {
        pattern: Box<Pattern>,
        def: DefId,
        typ: MonoType,
    },
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct RecordExprField {
    pub name: Name,
    pub value: ElaboratedExpr,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum RecordSpreadExpr {
    Head(Box<ElaboratedExpr>),
    Tail(Box<ElaboratedExpr>),
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct RecordPatternField {
    pub name: Name,
    pub pattern: Pattern,
    pub default: Option<ElaboratedExpr>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum RecordSpreadPattern {
    Head(Box<Pattern>),
    Tail(Box<Pattern>),
}

fn validate_concrete_type(
    ty: &Type,
    bound_vars: &mut BTreeSet<TypeVar>,
) -> Result<(), ConcreteTypeError> {
    match ty {
        Type::Unknown => Err(ConcreteTypeError::Unknown),
        Type::Var(var) if !bound_vars.contains(var) => Err(ConcreteTypeError::FreeVar(var.clone())),
        Type::Var(_) | Type::Never | Type::Any => Ok(()),
        Type::Named { args, .. } => args
            .iter()
            .try_for_each(|arg| validate_concrete_type_arg(arg, bound_vars)),
        Type::Fun {
            param,
            param_effect,
            ret_effect,
            ret,
        } => {
            validate_concrete_type(param, bound_vars)?;
            validate_concrete_type(param_effect, bound_vars)?;
            validate_concrete_type(ret_effect, bound_vars)?;
            validate_concrete_type(ret, bound_vars)
        }
        Type::Tuple(items) | Type::Union(items) | Type::Inter(items) => items
            .iter()
            .try_for_each(|item| validate_concrete_type(item, bound_vars)),
        Type::Record(record) => {
            for field in &record.fields {
                validate_concrete_type(&field.value, bound_vars)?;
            }
            if let Some(spread) = &record.spread {
                validate_record_spread(spread, bound_vars)?;
            }
            Ok(())
        }
        Type::Variant(variant) => {
            for case in &variant.cases {
                validate_variant_case(case, bound_vars)?;
            }
            if let Some(tail) = &variant.tail {
                validate_concrete_type(tail, bound_vars)?;
            }
            Ok(())
        }
        Type::Row { items, tail } => {
            for item in items {
                validate_concrete_type(item, bound_vars)?;
            }
            validate_concrete_type(tail, bound_vars)
        }
        Type::Recursive { var, body } => {
            let inserted = bound_vars.insert(var.clone());
            let result = validate_concrete_type(body, bound_vars);
            if inserted {
                bound_vars.remove(var);
            }
            result
        }
    }
}

fn validate_concrete_type_arg(
    arg: &TypeArg,
    bound_vars: &mut BTreeSet<TypeVar>,
) -> Result<(), ConcreteTypeError> {
    match arg {
        TypeArg::Type(ty) => validate_concrete_type(ty, bound_vars),
        TypeArg::Bounds(bounds) => {
            if let Some(lower) = &bounds.lower {
                validate_concrete_type(lower, bound_vars)?;
            }
            if let Some(upper) = &bounds.upper {
                validate_concrete_type(upper, bound_vars)?;
            }
            Ok(())
        }
    }
}

fn validate_record_spread(
    spread: &RecordSpread,
    bound_vars: &mut BTreeSet<TypeVar>,
) -> Result<(), ConcreteTypeError> {
    match spread {
        RecordSpread::Head(ty) | RecordSpread::Tail(ty) => validate_concrete_type(ty, bound_vars),
    }
}

fn validate_variant_case(
    case: &VariantCase,
    bound_vars: &mut BTreeSet<TypeVar>,
) -> Result<(), ConcreteTypeError> {
    case.payloads
        .iter()
        .try_for_each(|payload| validate_concrete_type(payload, bound_vars))
}

fn clone_expr_without_boundary_spine_recursion(expr: &ElaboratedExpr) -> ElaboratedExpr {
    enum Frame<'a> {
        Apply {
            comp: &'a MonoComputation,
            arg: &'a ElaboratedExpr,
        },
        Select {
            comp: &'a MonoComputation,
            field: &'a Name,
        },
        Variant {
            comp: &'a MonoComputation,
            tag: &'a Name,
        },
        MakeThunk {
            comp: &'a MonoComputation,
            thunk: &'a EffectiveThunkType,
        },
        LocalPushId {
            comp: &'a MonoComputation,
            id: &'a EffectIdVar,
        },
        AddId {
            comp: &'a MonoComputation,
            id: &'a EffectIdRef,
            allowed: &'a MonoEffect,
            active: bool,
        },
        ForceThunk {
            comp: &'a MonoComputation,
            source: &'a EffectiveThunkType,
            target: &'a MonoComputation,
        },
        Cast {
            comp: &'a MonoComputation,
            source: &'a MonoType,
            target: &'a MonoType,
        },
        FunctionAdapter {
            comp: &'a MonoComputation,
            adapter: &'a FunctionAdapter,
        },
        Pack {
            comp: &'a MonoComputation,
            var: &'a TypeVar,
        },
    }

    let mut current = expr;
    let mut frames = Vec::new();
    loop {
        match &current.kind {
            ElaboratedExprKind::Apply { callee, arg } => {
                frames.push(Frame::Apply {
                    comp: &current.comp,
                    arg,
                });
                current = callee;
            }
            ElaboratedExprKind::Select { base, field } => {
                frames.push(Frame::Select {
                    comp: &current.comp,
                    field,
                });
                current = base;
            }
            ElaboratedExprKind::Variant {
                tag,
                value: Some(value),
            } => {
                frames.push(Frame::Variant {
                    comp: &current.comp,
                    tag,
                });
                current = value;
            }
            ElaboratedExprKind::MakeThunk { body, thunk } => {
                frames.push(Frame::MakeThunk {
                    comp: &current.comp,
                    thunk,
                });
                current = body;
            }
            ElaboratedExprKind::LocalPushId { id, body } => {
                frames.push(Frame::LocalPushId {
                    comp: &current.comp,
                    id,
                });
                current = body;
            }
            ElaboratedExprKind::AddId {
                id,
                allowed,
                active,
                thunk,
            } => {
                frames.push(Frame::AddId {
                    comp: &current.comp,
                    id,
                    allowed,
                    active: *active,
                });
                current = thunk;
            }
            ElaboratedExprKind::ForceThunk {
                thunk,
                source,
                target,
            } => {
                frames.push(Frame::ForceThunk {
                    comp: &current.comp,
                    source,
                    target,
                });
                current = thunk;
            }
            ElaboratedExprKind::Cast {
                expr,
                source,
                target,
            } => {
                frames.push(Frame::Cast {
                    comp: &current.comp,
                    source,
                    target,
                });
                current = expr;
            }
            ElaboratedExprKind::FunctionAdapter { function, adapter } => {
                frames.push(Frame::FunctionAdapter {
                    comp: &current.comp,
                    adapter,
                });
                current = function;
            }
            ElaboratedExprKind::Pack { var, expr } => {
                frames.push(Frame::Pack {
                    comp: &current.comp,
                    var,
                });
                current = expr;
            }
            _ => break,
        }
    }

    let mut cloned = ElaboratedExpr {
        comp: current.comp.clone(),
        kind: current.kind.clone(),
    };
    for frame in frames.into_iter().rev() {
        cloned = match frame {
            Frame::Apply { comp, arg } => ElaboratedExpr {
                comp: comp.clone(),
                kind: ElaboratedExprKind::Apply {
                    callee: Box::new(cloned),
                    arg: Box::new(arg.clone()),
                },
            },
            Frame::Select { comp, field } => ElaboratedExpr {
                comp: comp.clone(),
                kind: ElaboratedExprKind::Select {
                    base: Box::new(cloned),
                    field: field.clone(),
                },
            },
            Frame::Variant { comp, tag } => ElaboratedExpr {
                comp: comp.clone(),
                kind: ElaboratedExprKind::Variant {
                    tag: tag.clone(),
                    value: Some(Box::new(cloned)),
                },
            },
            Frame::MakeThunk { comp, thunk } => ElaboratedExpr {
                comp: comp.clone(),
                kind: ElaboratedExprKind::MakeThunk {
                    body: Box::new(cloned),
                    thunk: thunk.clone(),
                },
            },
            Frame::LocalPushId { comp, id } => ElaboratedExpr {
                comp: comp.clone(),
                kind: ElaboratedExprKind::LocalPushId {
                    id: *id,
                    body: Box::new(cloned),
                },
            },
            Frame::AddId {
                comp,
                id,
                allowed,
                active,
            } => ElaboratedExpr {
                comp: comp.clone(),
                kind: ElaboratedExprKind::AddId {
                    id: *id,
                    allowed: allowed.clone(),
                    active,
                    thunk: Box::new(cloned),
                },
            },
            Frame::ForceThunk {
                comp,
                source,
                target,
            } => ElaboratedExpr {
                comp: comp.clone(),
                kind: ElaboratedExprKind::ForceThunk {
                    thunk: Box::new(cloned),
                    source: source.clone(),
                    target: target.clone(),
                },
            },
            Frame::Cast {
                comp,
                source,
                target,
            } => ElaboratedExpr {
                comp: comp.clone(),
                kind: ElaboratedExprKind::Cast {
                    expr: Box::new(cloned),
                    source: source.clone(),
                    target: target.clone(),
                },
            },
            Frame::FunctionAdapter { comp, adapter } => ElaboratedExpr {
                comp: comp.clone(),
                kind: ElaboratedExprKind::FunctionAdapter {
                    function: Box::new(cloned),
                    adapter: adapter.clone(),
                },
            },
            Frame::Pack { comp, var } => ElaboratedExpr {
                comp: comp.clone(),
                kind: ElaboratedExprKind::Pack {
                    var: var.clone(),
                    expr: Box::new(cloned),
                },
            },
        };
    }
    cloned
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn concrete_type_rejects_unknown_and_free_vars() {
        assert_eq!(
            ConcreteType::try_from_type(Type::Unknown),
            Err(ConcreteTypeError::Unknown)
        );
        assert_eq!(
            ConcreteType::try_from_type(Type::Var(TypeVar("a".to_string()))),
            Err(ConcreteTypeError::FreeVar(TypeVar("a".to_string())))
        );
    }

    #[test]
    fn concrete_type_allows_bound_recursive_vars_and_top_bottom() {
        assert!(ConcreteType::try_from_type(Type::Any).is_ok());
        assert!(ConcreteType::try_from_type(Type::Never).is_ok());
        assert!(
            ConcreteType::try_from_type(Type::Recursive {
                var: TypeVar("a".to_string()),
                body: Box::new(Type::Var(TypeVar("a".to_string()))),
            })
            .is_ok()
        );
    }

    #[test]
    fn force_thunk_keeps_source_and_target_boundary() {
        let int = MonoType::Value(named_value_type("int"));
        let effect = MonoEffect::new(named_value_type("io"));
        let thunk = EffectiveThunkType {
            effect: effect.clone(),
            value: Box::new(int.clone()),
        };
        let target = MonoComputation {
            value: int.clone(),
            effect: effect.clone(),
        };
        let thunk_expr = ElaboratedExpr::new(
            ElaboratedExprKind::Ref(RefId(1)),
            MonoComputation {
                value: MonoType::EffectiveThunk(thunk.clone()),
                effect: effect.clone(),
            },
        );

        let forced = ElaboratedExpr::new(
            ElaboratedExprKind::ForceThunk {
                thunk: Box::new(thunk_expr),
                source: thunk.clone(),
                target: target.clone(),
            },
            target,
        );

        let ElaboratedExprKind::ForceThunk { source, target, .. } = forced.kind else {
            panic!("expected force thunk");
        };
        assert_eq!(source, thunk);
        assert_eq!(target.value, int);
        assert_eq!(target.effect, effect);
    }

    #[test]
    fn function_adapter_carries_hygiene_plan_for_first_class_function_values() {
        let int = MonoType::Value(named_value_type("int"));
        let io = MonoEffect::new(named_value_type("io"));
        let source = FunctionBoundary {
            param: int.clone(),
            param_effect: io.clone(),
            ret_effect: io.clone(),
            ret: int.clone(),
        };
        let target = FunctionBoundary {
            param: int.clone(),
            param_effect: io.clone(),
            ret_effect: io.clone(),
            ret: int,
        };
        let local = EffectIdVar(0);
        let adapter = FunctionAdapter {
            source: source.clone(),
            target: target.clone(),
            call: FunctionAdapterCall {
                local_scope: Some(local),
                result_boundaries: vec![FunctionResultBoundary::AddId {
                    id: EffectIdRef::Var(local),
                    allowed: io.clone(),
                    active: false,
                }],
            },
        };

        let adapted = ElaboratedExpr::new(
            ElaboratedExprKind::FunctionAdapter {
                function: Box::new(ElaboratedExpr::new(
                    ElaboratedExprKind::Ref(RefId(1)),
                    MonoComputation {
                        value: MonoType::Value(function_type(&source)),
                        effect: MonoEffect::new(
                            ConcreteType::try_from_type(Type::Never).expect("Never is concrete"),
                        ),
                    },
                )),
                adapter: adapter.clone(),
            },
            MonoComputation {
                value: MonoType::Value(function_type(&target)),
                effect: MonoEffect::new(
                    ConcreteType::try_from_type(Type::Never).expect("Never is concrete"),
                ),
            },
        );

        let ElaboratedExprKind::FunctionAdapter { adapter, .. } = adapted.kind else {
            panic!("expected function adapter");
        };
        assert_eq!(adapter.call.local_scope, Some(local));
        assert_eq!(
            adapter.call.result_boundaries,
            vec![FunctionResultBoundary::AddId {
                id: EffectIdRef::Var(local),
                allowed: io,
                active: false,
            }]
        );
    }

    #[test]
    fn clones_deep_boundary_spine_without_recursing() {
        let int = MonoType::Value(named_value_type("int"));
        let effect = MonoEffect::new(named_value_type("io"));
        let comp = MonoComputation {
            value: int.clone(),
            effect: effect.clone(),
        };
        let mut expr =
            ElaboratedExpr::new(ElaboratedExprKind::Lit(Lit::Int("1".to_string())), comp);

        for _ in 0..20_000 {
            expr = ElaboratedExpr::new(
                ElaboratedExprKind::Cast {
                    expr: Box::new(expr),
                    source: int.clone(),
                    target: int.clone(),
                },
                MonoComputation {
                    value: int.clone(),
                    effect: effect.clone(),
                },
            );
        }

        let cloned = expr.clone();

        assert_eq!(cloned.comp.value, int);
        std::mem::forget(expr);
        std::mem::forget(cloned);
    }

    fn named_value_type(name: &str) -> ConcreteType {
        ConcreteType::try_from_type(Type::Named {
            path: Path::from_name(Name(name.to_string())),
            args: Vec::new(),
        })
        .expect("named type is concrete")
    }

    fn function_type(boundary: &FunctionBoundary) -> ConcreteType {
        ConcreteType::try_from_type(Type::Fun {
            param: Box::new(boundary_value_type(&boundary.param)),
            param_effect: Box::new(boundary.param_effect.row().as_type().clone()),
            ret_effect: Box::new(boundary.ret_effect.row().as_type().clone()),
            ret: Box::new(boundary_value_type(&boundary.ret)),
        })
        .expect("function boundary is concrete")
    }

    fn boundary_value_type(typ: &MonoType) -> Type {
        match typ {
            MonoType::Value(value) => value.as_type().clone(),
            MonoType::EffectiveThunk(_) => panic!("test helper only builds value function types"),
        }
    }
}
