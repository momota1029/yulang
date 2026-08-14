//! Scope-bound immutable view shell. Production queries cut over in SS6.

use poly::types::TypeArena;

use super::gateway::StructuralData;
use crate::constraints::proof::ProofStructuralSnapshotId;

pub(in crate::constraints) struct ScopedQueryView<'query> {
    data: &'query StructuralData,
    snapshot: ProofStructuralSnapshotId,
    type_shapes: &'query TypeArena,
}

impl ScopedQueryView<'_> {
    pub(in crate::constraints::structural_kernel) fn new<'query>(
        data: &'query StructuralData,
        type_shapes: &'query TypeArena,
        snapshot: ProofStructuralSnapshotId,
    ) -> ScopedQueryView<'query> {
        ScopedQueryView {
            data,
            snapshot,
            type_shapes,
        }
    }

    pub(in crate::constraints) fn snapshot(&self) -> ProofStructuralSnapshotId {
        self.snapshot
    }

    pub(in crate::constraints) fn type_shapes(&self) -> &TypeArena {
        self.type_shapes
    }

    pub(in crate::constraints) fn is_empty_shadow(&self) -> bool {
        let _ = self.data;
        true
    }
}
