//! Scope-bound immutable view shell. Production queries cut over in SS6.

use poly::types::{Pos, PosId, TypeArena};

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
}

pub(in crate::constraints) struct ScopedQueryView<'query> {
    data: &'query StructuralData,
    type_shapes: ImmutableTypeShapeView<'query>,
}

impl ScopedQueryView<'_> {
    pub(in crate::constraints::structural_kernel) fn new<'query>(
        data: &'query StructuralData,
        type_shapes: ImmutableTypeShapeView<'query>,
    ) -> ScopedQueryView<'query> {
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
    pub(in crate::constraints) fn raw_shadow_probe(&self) -> &u64 {
        self.data.raw_shadow_probe()
    }
}
