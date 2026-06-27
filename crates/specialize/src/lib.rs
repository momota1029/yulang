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

pub(crate) use lib_support::boundary::*;
pub(crate) use lib_support::convert::*;
pub use mono;
pub use specialize2::{
    RuntimeEvidenceEffectSubtraction, RuntimeEvidenceExprType, RuntimeEvidenceGraph,
    RuntimeEvidenceRowResidual, RuntimeEvidenceSlot, RuntimeEvidenceSlotKind,
    RuntimeEvidenceStackWeight, RuntimeEvidenceSurface, RuntimeEvidenceTask,
    RuntimeEvidenceTaskOwner, RuntimeEvidenceTypeAtExpr, RuntimeEvidenceTypeAtPat,
    RuntimeEvidenceTypePathStep, RuntimeEvidenceTypeRole, RuntimeEvidenceTypeclassResolution,
    RuntimeEvidenceWeightedSlotEdge, RuntimeEvidenceWeightedTypeBound, SpecializeOutput,
    format_runtime_evidence_surface,
};

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

pub fn specialize(arena: &poly_expr::Arena) -> Result<Program, SpecializeError> {
    specialize2::specialize(arena)
}

pub fn specialize_with_runtime_evidence(
    arena: &poly_expr::Arena,
) -> Result<SpecializeOutput, SpecializeError> {
    specialize2::specialize_with_runtime_evidence(arena)
}

pub fn specialize2(arena: &poly_expr::Arena) -> Result<Program, SpecializeError> {
    specialize2::specialize(arena)
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
        member: DefId,
        receiver: Type,
    },
    AmbiguousTypeclassMethod {
        member: DefId,
        receiver: Type,
        candidates: Vec<DefId>,
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

impl fmt::Display for SpecializeError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::MissingDef { def } => write!(f, "missing def d{}", def.0),
            Self::MissingScheme { def } => write!(f, "missing scheme for d{}", def.0),
            Self::MissingBody { def } => write!(f, "missing body for d{}", def.0),
            Self::UnsupportedDefKind { def, kind } => {
                write!(f, "unsupported def kind for d{}: {kind:?}", def.0)
            }
            Self::UnsupportedSchemeFeature { def, feature } => {
                write!(f, "unsupported scheme feature for d{}: {feature:?}", def.0,)
            }
            Self::ConflictingTypeSubstitution {
                def,
                var,
                existing,
                incoming,
            } => {
                write!(
                    f,
                    "conflicting type substitution for d{} 't{}: {} vs {}",
                    def.0,
                    var,
                    mono::dump::dump_type(existing),
                    mono::dump::dump_type(incoming),
                )
            }
            Self::ConflictingExprType {
                expr,
                role,
                existing,
                incoming,
            } => {
                write!(
                    f,
                    "conflicting {role:?} expression type for e{expr}: {} vs {}",
                    mono::dump::dump_type(existing),
                    mono::dump::dump_type(incoming),
                )
            }
            Self::MissingExprType { expr, role } => {
                write!(f, "missing {role:?} expression type for e{expr}")
            }
            Self::ConflictingTypeCandidates {
                slot,
                existing,
                incoming,
            } => {
                write!(
                    f,
                    "conflicting type candidates for slot {slot}: {} vs {}",
                    mono::dump::dump_type(existing),
                    mono::dump::dump_type(incoming),
                )
            }
            Self::UnsatisfiedSubtype { lower, upper } => {
                write!(
                    f,
                    "unsatisfied subtype constraint: {} <: {}",
                    mono::dump::dump_type(lower),
                    mono::dump::dump_type(upper),
                )
            }
            Self::UndeterminedTypeSlot { slot } => {
                write!(f, "could not determine concrete type for slot {slot}")
            }
            Self::UnresolvedStackWeight { ty } => {
                write!(
                    f,
                    "could not eliminate stack-weighted type {}",
                    mono::dump::dump_type(ty),
                )
            }
            Self::InvalidTypeSlot { slot } => write!(f, "invalid type slot {slot}"),
            Self::UnresolvedRef { ref_id } => write!(f, "unresolved ref r{ref_id}"),
            Self::UnresolvedTypeclassMethod { member, receiver } => {
                write!(
                    f,
                    "unresolved typeclass method d{} for receiver {}",
                    member.0,
                    mono::dump::dump_type(receiver),
                )
            }
            Self::AmbiguousTypeclassMethod {
                member,
                receiver,
                candidates,
            } => {
                let candidates = candidates
                    .iter()
                    .map(|candidate| format!("d{}", candidate.0))
                    .collect::<Vec<_>>()
                    .join(", ");
                write!(
                    f,
                    "ambiguous typeclass method d{} for receiver {}: {}",
                    member.0,
                    mono::dump::dump_type(receiver),
                    candidates,
                )
            }
            Self::InternalMissingInstance { instance } => {
                write!(f, "internal missing mono instance m{}", instance.0)
            }
        }
    }
}

impl std::error::Error for SpecializeError {}
