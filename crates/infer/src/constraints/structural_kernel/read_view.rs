//! Scope-bound immutable view shell. Production proof reads cut over in SS2; the remaining
//! structural families follow in SS3--SS5.

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
