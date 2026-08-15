//! Scope-bound immutable view shell. Production proof reads cut over in SS2; the remaining
//! structural families follow in SS3--SS5.

use poly::roles::RoleConstraint;
use poly::types::{Neg, NegId, Neu, NeuId, Pos, PosId, TypeArena, TypeVar};
use rustc_hash::FxHashSet;

use super::gateway::StructuralData;

#[derive(Clone, Copy)]
pub(in crate::constraints) struct ImmutableTypeShapeView<'query> {
    types: &'query TypeArena,
}

impl ImmutableTypeShapeView<'_> {
    pub(in crate::constraints::structural_kernel) fn new(
        types: &TypeArena,
    ) -> ImmutableTypeShapeView<'_> {
        ImmutableTypeShapeView { types }
    }

    pub(in crate::constraints) fn is_var_pos(self, id: PosId) -> bool {
        matches!(self.types.pos(id), Pos::Var(_))
    }

    pub(in crate::constraints::structural_kernel) fn pos_var(self, id: PosId) -> Option<TypeVar> {
        match self.types.pos(id) {
            Pos::Var(var) => Some(*var),
            _ => None,
        }
    }

    #[allow(
        dead_code,
        reason = "row 1 slice 1 wires this shape read before slices 2 and 3 migrate its callers"
    )]
    pub(in crate::constraints::structural_kernel) fn pos_shape(self, id: PosId) -> Pos {
        self.types.pos(id).clone()
    }

    #[allow(
        dead_code,
        reason = "row 1 slice 1 wires this shape read before slices 2 and 3 migrate its callers"
    )]
    pub(in crate::constraints::structural_kernel) fn neg_shape(self, id: NegId) -> Neg {
        self.types.neg(id).clone()
    }

    #[allow(
        dead_code,
        reason = "row 1 slice 1 wires this shape read before slices 2 and 3 migrate its callers"
    )]
    pub(in crate::constraints::structural_kernel) fn neu_shape(self, id: NeuId) -> Neu {
        self.types.neu(id).clone()
    }

    #[allow(
        dead_code,
        reason = "row 1 slice 1 wires this shape read before slices 2 and 3 migrate its callers"
    )]
    pub(in crate::constraints::structural_kernel) fn role_constraint_raw_vars(
        self,
        constraint: &RoleConstraint,
    ) -> FxHashSet<TypeVar> {
        constraint.raw_vars(self.types)
    }

    pub(in crate::constraints::structural_kernel) fn neg_var(self, id: NegId) -> Option<TypeVar> {
        match self.types.neg(id) {
            Neg::Var(var) => Some(*var),
            _ => None,
        }
    }
}

pub(in crate::constraints) struct ScopedQueryView<'query> {
    data: &'query StructuralData,
    type_shapes: ImmutableTypeShapeView<'query>,
}

impl<'query> ScopedQueryView<'query> {
    pub(in crate::constraints::structural_kernel) fn new(
        data: &'query StructuralData,
        type_shapes: ImmutableTypeShapeView<'query>,
    ) -> Self {
        ScopedQueryView { data, type_shapes }
    }

    pub(in crate::constraints) fn type_shapes(&self) -> ImmutableTypeShapeView<'_> {
        self.type_shapes
    }

    pub(in crate::constraints) fn is_empty_shadow(&self) -> bool {
        let _ = self.data;
        true
    }

    #[cfg(cpk_sv_d_ss1_rf_ui_raw_escape)]
    pub(in crate::constraints) fn raw_shadow_probe(&self) -> &'query u64 {
        self.data.raw_shadow_probe()
    }

    #[cfg(cpk_sv_d_ss1_rf_ui_cursor_escape)]
    pub(in crate::constraints) fn shadow_cursor(&self) -> ShadowQueryCursor<'query> {
        ShadowQueryCursor {
            value: self.data.raw_shadow_probe(),
        }
    }
}

#[cfg(cpk_sv_d_ss1_rf_ui_cursor_escape)]
pub(in crate::constraints::structural_kernel) struct ShadowQueryCursor<'query> {
    value: &'query u64,
}

#[cfg(cpk_sv_d_ss1_rf_ui_cursor_escape)]
impl ShadowQueryCursor<'_> {
    pub(in crate::constraints::structural_kernel) fn value(&self) -> u64 {
        *self.value
    }
}
