//! Constraint solver core for principal elaboration.
//!
//! This module is the replacement nucleus for `constraints.rs`. Types here are
//! plain interned trees. Bounds, intervals, and role-associated outputs live in
//! the graph layer and are never stored inside nominal type arguments.

mod graph;
mod principal;
mod types;

pub use graph::{ConstraintGraph, TypeInterval, VarBounds};
pub use principal::{
    PrincipalImportError, PrincipalTypeForm, PrincipalTypeInstance, PrincipalTypeInstantiator,
};
pub use types::{
    MonoVarId, RecordShape, RowShape, TypeArena, TypeId, TypeKind, TypeVarKind, VariantShape,
};
