//! `poly::Arena` から `mono::Program` を作る単一化 crate。
//!
//! この crate は現行 yulang 系の後段入口であり、旧 typed IR や旧 monomorphize の evidence を読まない。
//! 主型と文脈型から monomorphize 用の signature を作り、到達した定義だけを `mono` instance 化する。

#![forbid(unsafe_code)]

mod hygiene;
mod lib_support;
mod roles;
mod solve;
mod specialize2;
mod std_types;
#[cfg(test)]
mod tests;
mod types;

use std::collections::{HashMap, HashSet};
use std::fmt;

use mono::{
    Block, CaseArm, CatchArm, ComputationType, DefId, EffectiveThunkType, Expr, ExprKind, Instance,
    InstanceId, InstanceSource, ListViewConstructors, Lit, Pat, PrimitiveContext, PrimitiveOp,
    Program, RangeConstructors, RecordField, RecordSpread, Root, SelectResolution, Stmt, Type, Vis,
};
use poly::expr as poly_expr;
use poly::provenance::SubtypeProvenanceSidecar;

pub(crate) use lib_support::boundary::*;
pub(crate) use lib_support::convert::*;
pub use mono;
pub use specialize2::{
    RuntimeEvidenceBoundaryCandidate, RuntimeEvidenceEffectSubtraction, RuntimeEvidenceExprType,
    RuntimeEvidenceGraph, RuntimeEvidenceKnownStateAccessRole,
    RuntimeEvidenceKnownStateContinuationSemantics, RuntimeEvidenceKnownStateHandler,
    RuntimeEvidenceKnownStateHandlerSource, RuntimeEvidenceNode, RuntimeEvidenceNodeEvidenceRef,
    RuntimeEvidenceNodeKind, RuntimeEvidenceRowResidual, RuntimeEvidenceSite,
    RuntimeEvidenceSiteKind, RuntimeEvidenceSlot, RuntimeEvidenceSlotKind,
    RuntimeEvidenceStackWeight, RuntimeEvidenceStaticRoute,
    RuntimeEvidenceStaticRouteDynamicReason, RuntimeEvidenceStaticRouteResolution,
    RuntimeEvidenceSurface, RuntimeEvidenceTask, RuntimeEvidenceTaskOwner,
    RuntimeEvidenceTypeAtExpr, RuntimeEvidenceTypeAtPat, RuntimeEvidenceTypePathStep,
    RuntimeEvidenceTypeRole, RuntimeEvidenceTypeclassResolution, RuntimeEvidenceWeightedSlotEdge,
    RuntimeEvidenceWeightedTypeBound, SpecializeOutput, format_runtime_evidence_surface,
};

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RoleMethodCheckOutcome {
    pub select: poly_expr::SelectId,
    pub member: poly_expr::DefId,
    pub receiver: Type,
    pub resolution: RoleMethodCheckResolution,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum RoleMethodCheckResolution {
    Resolved(poly_expr::DefId),
    DefaultBody,
    Unresolved,
    Ambiguous(Vec<poly_expr::DefId>),
}

#[derive(Debug, Clone, Default)]
pub struct Specializer {
    instances: Vec<Option<Instance>>,
    instance_by_key: HashMap<InstanceKey, InstanceId>,
    active_instance_signatures: HashMap<InstanceId, Type>,
    local_defs: HashSet<poly_expr::DefId>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
struct InstanceKey {
    def: poly_expr::DefId,
    ty: Type,
}

pub fn specialize(
    arena: &poly_expr::Arena,
    sidecar: &SubtypeProvenanceSidecar,
) -> Result<Program, SpecializeError> {
    specialize2::specialize(arena, sidecar)
}

pub fn specialize_with_runtime_evidence(
    arena: &poly_expr::Arena,
    sidecar: &SubtypeProvenanceSidecar,
) -> Result<SpecializeOutput, SpecializeError> {
    specialize2::specialize_with_runtime_evidence(arena, sidecar)
}

pub fn specialize_with_runtime_evidence_and_application_provenance(
    arena: &poly_expr::Arena,
    sidecar: &SubtypeProvenanceSidecar,
    source_applications: impl IntoIterator<Item = poly_expr::ExprId>,
) -> Result<SpecializeOutput, SpecializeError> {
    specialize2::specialize_with_runtime_evidence_and_application_provenance(
        arena,
        sidecar,
        source_applications,
    )
}

pub fn specialize_with_runtime_evidence_and_source_provenance(
    arena: &poly_expr::Arena,
    sidecar: &SubtypeProvenanceSidecar,
    source_applications: impl IntoIterator<Item = poly_expr::ExprId>,
    source_selections: impl IntoIterator<Item = poly_expr::SelectId>,
) -> Result<SpecializeOutput, SpecializeError> {
    specialize2::specialize_with_runtime_evidence_and_source_provenance(
        arena,
        sidecar,
        source_applications,
        source_selections,
    )
}

pub fn specialize2(
    arena: &poly_expr::Arena,
    sidecar: &SubtypeProvenanceSidecar,
) -> Result<Program, SpecializeError> {
    specialize2::specialize(arena, sidecar)
}

pub fn role_method_check(
    arena: &poly_expr::Arena,
    sidecar: &SubtypeProvenanceSidecar,
) -> Vec<RoleMethodCheckOutcome> {
    specialize2::role_method_check(arena, sidecar)
}

pub fn specialize_roots(
    arena: &poly_expr::Arena,
    roots: impl IntoIterator<Item = poly_expr::DefId>,
) -> Result<Program, SpecializeError> {
    Specializer::new().specialize_roots(arena, roots)
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SpecializeError {
    MissingDef {
        def: DefId,
    },
    MissingScheme {
        def: DefId,
    },
    MissingBody {
        def: DefId,
    },
    UnsupportedDefKind {
        def: DefId,
        kind: DefKind,
    },
    UnsupportedSchemeFeature {
        def: DefId,
        feature: SchemeFeature,
    },
    ConflictingTypeSubstitution {
        def: DefId,
        var: u32,
        existing: Type,
        incoming: Type,
    },
    ConflictingExprType {
        expr: u32,
        role: ExprTypeRole,
        existing: Type,
        incoming: Type,
    },
    MissingExprType {
        expr: u32,
        role: ExprTypeRole,
    },
    ConflictingTypeCandidates {
        slot: u32,
        existing: Type,
        incoming: Type,
    },
    UnsatisfiedSubtype {
        lower: Type,
        upper: Type,
        origin: Option<UnsatisfiedSubtypeOrigin>,
    },
    UndeterminedTypeSlot {
        slot: u32,
    },
    UnresolvedStackWeight {
        ty: Type,
    },
    InvalidTypeSlot {
        slot: u32,
    },
    UnresolvedRef {
        ref_id: u32,
    },
    UnresolvedTypeclassMethod {
        expr: u32,
        member: DefId,
        receiver: Type,
    },
    AmbiguousTypeclassMethod {
        expr: u32,
        member: DefId,
        receiver: Type,
        candidates: Vec<DefId>,
    },
    AmbiguousImplicitCast {
        actual: Type,
        expected: Type,
        candidates: Vec<poly_expr::DefId>,
        owner: Option<poly_expr::DefId>,
    },
    InternalMissingInstance {
        instance: InstanceId,
    },
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DefKind {
    Module,
    Let,
    Arg,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SchemeFeature {
    RolePredicates,
    RecursiveBounds,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ExprTypeRole {
    Actual,
    Expected,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum UnsatisfiedSubtypeOrigin {
    MissingRecordField {
        field: String,
        actual_fields: Vec<String>,
        select: Option<poly_expr::SelectId>,
    },
    MissingImplicitCast {
        source: Vec<String>,
        target: Vec<String>,
        owner: Option<poly_expr::DefId>,
    },
}

impl fmt::Display for SpecializeError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::MissingDef { .. } => write!(f, "missing definition"),
            Self::MissingScheme { .. } => write!(f, "missing type scheme"),
            Self::MissingBody { .. } => write!(f, "missing definition body"),
            Self::UnsupportedDefKind { kind, .. } => {
                write!(f, "unsupported definition kind: {}", format_def_kind(*kind))
            }
            Self::UnsupportedSchemeFeature { feature, .. } => {
                write!(
                    f,
                    "unsupported type scheme feature: {}",
                    format_scheme_feature(*feature),
                )
            }
            Self::ConflictingTypeSubstitution {
                existing, incoming, ..
            } => {
                write!(
                    f,
                    "conflicting type substitution: {} vs {}",
                    mono::dump::dump_type(existing),
                    mono::dump::dump_type(incoming),
                )
            }
            Self::ConflictingExprType {
                role,
                existing,
                incoming,
                ..
            } => {
                write!(
                    f,
                    "conflicting {} expression type: {} vs {}",
                    format_expr_type_role(*role),
                    mono::dump::dump_type(existing),
                    mono::dump::dump_type(incoming),
                )
            }
            Self::MissingExprType { role, .. } => {
                write!(
                    f,
                    "missing {} expression type",
                    format_expr_type_role(*role)
                )
            }
            Self::ConflictingTypeCandidates {
                existing, incoming, ..
            } => {
                write!(
                    f,
                    "conflicting type candidates: {} vs {}",
                    mono::dump::dump_type(existing),
                    mono::dump::dump_type(incoming),
                )
            }
            Self::UnsatisfiedSubtype {
                origin: Some(UnsatisfiedSubtypeOrigin::MissingImplicitCast { source, target, .. }),
                ..
            } => {
                write!(
                    f,
                    "cannot use `{}` where `{}` is required: no implicit cast from `{}` to `{}`",
                    source.join("::"),
                    target.join("::"),
                    source.join("::"),
                    target.join("::"),
                )
            }
            Self::UnsatisfiedSubtype { lower, upper, .. } => {
                write!(
                    f,
                    "unsatisfied subtype constraint: {} <: {}",
                    mono::dump::dump_type(lower),
                    mono::dump::dump_type(upper),
                )
            }
            Self::UndeterminedTypeSlot { .. } => {
                write!(f, "could not determine concrete type")
            }
            Self::UnresolvedStackWeight { ty } => {
                write!(
                    f,
                    "could not eliminate stack-weighted type {}",
                    mono::dump::dump_type(ty),
                )
            }
            Self::InvalidTypeSlot { .. } => write!(f, "invalid type slot"),
            Self::UnresolvedRef { .. } => write!(f, "unresolved reference"),
            Self::UnresolvedTypeclassMethod { receiver, .. } => {
                write!(
                    f,
                    "no role implementation satisfies this method call for receiver {}",
                    mono::dump::dump_type(receiver),
                )
            }
            Self::AmbiguousTypeclassMethod { receiver, .. } => {
                write!(
                    f,
                    "more than one role implementation satisfies this method call for receiver {}",
                    mono::dump::dump_type(receiver),
                )
            }
            Self::AmbiguousImplicitCast {
                actual,
                expected,
                candidates,
                ..
            } => {
                write!(
                    f,
                    "implicit cast from `{}` to `{}` is ambiguous: {} visible declarations match",
                    mono::dump::dump_type(actual),
                    mono::dump::dump_type(expected),
                    candidates.len(),
                )
            }
            Self::InternalMissingInstance { .. } => {
                write!(f, "internal specialization instance is missing")
            }
        }
    }
}

impl std::error::Error for SpecializeError {}

fn format_def_kind(kind: DefKind) -> &'static str {
    match kind {
        DefKind::Module => "module",
        DefKind::Let => "value binding",
        DefKind::Arg => "argument",
    }
}

fn format_scheme_feature(feature: SchemeFeature) -> &'static str {
    match feature {
        SchemeFeature::RolePredicates => "role predicates",
        SchemeFeature::RecursiveBounds => "recursive bounds",
    }
}

fn format_expr_type_role(role: ExprTypeRole) -> &'static str {
    match role {
        ExprTypeRole::Actual => "actual",
        ExprTypeRole::Expected => "expected",
    }
}
