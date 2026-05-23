use super::type_graph::build_type_graph;
use super::*;

#[derive(Debug, Clone, Default)]
pub(super) struct ConflictCastReport {
    pub(super) inserted_casts: usize,
    pub(super) unresolved_conflicts: usize,
}

pub(super) fn insert_conflict_casts_preview(module: &Module) -> ConflictCastReport {
    let (graph, _report) = build_type_graph(module);
    ConflictCastReport {
        inserted_casts: 0,
        unresolved_conflicts: graph.conflicts().len(),
    }
}
