use rowan::TextRange;

use crate::ids::{NegId, PosId, TypeVar};

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TypeOrigin {
    pub span: Option<TextRange>,
    pub kind: TypeOriginKind,
    pub label: Option<String>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TypeOriginKind {
    Literal,
    Binding,
    Param,
    Annotation,
    ApplicationResult,
    EffectOperation,
    FieldSelection,
    Synthetic,
    Unknown,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ConstraintCause {
    pub span: Option<TextRange>,
    pub reason: ConstraintReason,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ExpectedEdge {
    pub actual_tv: TypeVar,
    pub expected_tv: TypeVar,
    pub actual_eff: Option<TypeVar>,
    pub expected_eff: Option<TypeVar>,
    pub kind: ExpectedEdgeKind,
    pub cause: ConstraintCause,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum ExpectedEdgeKind {
    IfCondition,
    IfBranch,
    MatchGuard,
    MatchBranch,
    CatchGuard,
    CatchBranch,
    ApplicationArgument,
    Annotation,
    RecordField,
    VariantPayload,
    AssignmentValue,
    RepresentationCoerce,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ConstraintReason {
    ApplyArg,
    ApplyFunction,
    Annotation,
    RepresentationCoerce,
    ImplMember,
    IfCondition,
    IfBranch,
    MatchGuard,
    MatchBranch,
    CatchGuard,
    CatchBranch,
    AssignmentValue,
    BindingBody,
    FieldSelection,
    RowCompare,
    Structural,
    Unknown,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TypeError {
    pub cause: ConstraintCause,
    pub kind: TypeErrorKind,
    pub pos: PosId,
    pub neg: NegId,
    pub origins: Vec<TypeOrigin>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TypeErrorKind {
    ConstructorMismatch,
    TupleArityMismatch {
        pos_len: usize,
        neg_len: usize,
    },
    MissingRecordField {
        name: String,
    },
    ExpectedShape {
        expected: ExpectedShape,
    },
    MissingImpl {
        role: String,
        args: Vec<String>,
    },
    MissingImplMember {
        role: String,
        member: String,
    },
    UnknownImplMember {
        role: String,
        member: String,
    },
    AmbiguousImpl {
        role: String,
        args: Vec<String>,
        candidates: usize,
        previews: Vec<String>,
    },
    MissingImplPrerequisite {
        role: String,
        args: Vec<String>,
        prerequisite_role: String,
        prerequisite_args: Vec<String>,
    },
    AmbiguousImplPrerequisite {
        role: String,
        args: Vec<String>,
        prerequisite_role: String,
        prerequisite_args: Vec<String>,
        candidates: usize,
        previews: Vec<String>,
    },
    AmbiguousEffectMethod {
        method: String,
        effects: Vec<String>,
    },
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ExpectedShape {
    Function,
    Tuple,
    Record,
    Constructor,
}

impl TypeOrigin {
    pub fn unknown() -> Self {
        Self {
            span: None,
            kind: TypeOriginKind::Unknown,
            label: None,
        }
    }

    pub fn synthetic(label: impl Into<String>) -> Self {
        Self {
            span: None,
            kind: TypeOriginKind::Synthetic,
            label: Some(label.into()),
        }
    }
}

impl ConstraintCause {
    pub fn unknown() -> Self {
        Self {
            span: None,
            reason: ConstraintReason::Unknown,
        }
    }
}

pub fn type_error_vars(infer: &crate::solve::Infer, error: &TypeError) -> Vec<TypeVar> {
    origin_vars(infer, error.pos, error.neg)
}

pub(super) fn origin_vars(infer: &crate::solve::Infer, pos: PosId, neg: NegId) -> Vec<TypeVar> {
    let mut vars = Vec::new();
    let mut push = |tv: TypeVar| {
        if !vars.contains(&tv) {
            vars.push(tv);
        }
    };
    collect_pos_tvs(infer, pos, &mut push);
    collect_neg_tvs(infer, neg, &mut push);
    vars
}

fn collect_pos_tvs(infer: &crate::solve::Infer, id: PosId, out: &mut impl FnMut(TypeVar)) {
    use crate::types::Pos;
    match infer.arena.get_pos(id) {
        Pos::Bot => {}
        Pos::Var(tv) | Pos::Raw(tv) => out(tv),
        Pos::Atom(a) => a.args.iter().for_each(|(p, n)| {
            out(*p);
            out(*n);
        }),
        Pos::Forall(_, body) => collect_pos_tvs(infer, body, out),
        Pos::Con(_, args) => args.iter().for_each(|(p, n)| {
            collect_pos_tvs(infer, *p, out);
            collect_neg_tvs(infer, *n, out);
        }),
        Pos::Fun {
            arg,
            arg_eff,
            ret_eff,
            ret,
        } => {
            collect_neg_tvs(infer, arg, out);
            collect_neg_tvs(infer, arg_eff, out);
            collect_pos_tvs(infer, ret_eff, out);
            collect_pos_tvs(infer, ret, out);
        }
        Pos::Record(fields) => fields
            .iter()
            .for_each(|field| collect_pos_tvs(infer, field.value, out)),
        Pos::RecordTailSpread { fields, tail } => {
            fields
                .iter()
                .for_each(|field| collect_pos_tvs(infer, field.value, out));
            collect_pos_tvs(infer, tail, out);
        }
        Pos::RecordHeadSpread { tail, fields } => {
            collect_pos_tvs(infer, tail, out);
            fields
                .iter()
                .for_each(|field| collect_pos_tvs(infer, field.value, out));
        }
        Pos::PolyVariant(items) => items.iter().for_each(|(_, ps)| {
            ps.iter().for_each(|p| collect_pos_tvs(infer, *p, out));
        }),
        Pos::Tuple(items) => items.iter().for_each(|p| collect_pos_tvs(infer, *p, out)),
        Pos::Row(items, tail) => {
            items.iter().for_each(|p| collect_pos_tvs(infer, *p, out));
            collect_pos_tvs(infer, tail, out);
        }
        Pos::Union(a, b) => {
            collect_pos_tvs(infer, a, out);
            collect_pos_tvs(infer, b, out);
        }
    }
}

fn collect_neg_tvs(infer: &crate::solve::Infer, id: NegId, out: &mut impl FnMut(TypeVar)) {
    use crate::types::Neg;
    match infer.arena.get_neg(id) {
        Neg::Top => {}
        Neg::Var(tv) => out(tv),
        Neg::Atom(a) => a.args.iter().for_each(|(p, n)| {
            out(*p);
            out(*n);
        }),
        Neg::Forall(_, body) => collect_neg_tvs(infer, body, out),
        Neg::Con(_, args) => args.iter().for_each(|(p, n)| {
            collect_pos_tvs(infer, *p, out);
            collect_neg_tvs(infer, *n, out);
        }),
        Neg::Fun {
            arg,
            arg_eff,
            ret_eff,
            ret,
        } => {
            collect_pos_tvs(infer, arg, out);
            collect_pos_tvs(infer, arg_eff, out);
            collect_neg_tvs(infer, ret_eff, out);
            collect_neg_tvs(infer, ret, out);
        }
        Neg::Record(fields) => fields
            .iter()
            .for_each(|field| collect_neg_tvs(infer, field.value, out)),
        Neg::PolyVariant(items) => items.iter().for_each(|(_, ns)| {
            ns.iter().for_each(|n| collect_neg_tvs(infer, *n, out));
        }),
        Neg::Tuple(items) => items.iter().for_each(|n| collect_neg_tvs(infer, *n, out)),
        Neg::Row(items, tail) => {
            items.iter().for_each(|n| collect_neg_tvs(infer, *n, out));
            collect_neg_tvs(infer, tail, out);
        }
        Neg::Intersection(a, b) => {
            collect_neg_tvs(infer, a, out);
            collect_neg_tvs(infer, b, out);
        }
    }
}
